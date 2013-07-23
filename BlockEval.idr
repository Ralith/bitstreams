module Main

import BitStream

%default total

Carries : Type
Carries = List Bits64

data EvalBlock : Type -> Type where
  EB : (Carries -> (Carries, t, Carries)) -> EvalBlock t

runEval : Carries -> EvalBlock t -> (Carries, t)
runEval cs (EB f) = let (nc, x, _) = f cs in (nc, x)

instance Functor EvalBlock where
  map f (EB g) = EB (\cs => let (nc, r, cs') = g cs in (nc, (f r), cs'))

instance Applicative EvalBlock where
  pure x = EB (\cs => ([], x, cs))
  (EB f) <$> (EB x) = EB (\cs => let (nc, f', cs') = f cs in
                                 let (nc', x', cs'') = x cs' in
                                 (nc ++ nc', (f' x'), cs''))

instance Monad EvalBlock where
  (EB x) >>= f = EB (\cs => let (nc, x', cs') = x cs in
                            let EB g = f x' in
                            let (nc', r, cs'') = g cs' in
                            (nc ++ nc', r, cs''))

(>>=) : EvalBlock a -> (a -> EvalBlock b) -> EvalBlock b
(>>=) x f = Prelude.Monad.(>>=) x f

popCarry : EvalBlock Bits64
popCarry = EB (\cs => ([], fromMaybe 0 (head' cs), fromMaybe [] (tail' cs)))

tellCarry : Bits64 -> EvalBlock ()
tellCarry c = EB (\cs => ([c], (), cs))

evalBlockTy : Ty -> Type
evalBlockTy TyStream = EvalBlock Bits64x2
evalBlockTy (TyOutput n) = EvalBlock (Vect Bits64x2 n)
evalBlockTy (TyFun t) = Bits64x2 -> (evalBlockTy t)

boolToB64 : Bool -> Bits64
boolToB64 True = 1
boolToB64 False = 0

addWithCarry : Bits64 -> Bits64 -> (Bits64, Bits64)
addWithCarry l r = (boolToB64 ((18446744073709551615 - r) < l), l + r)

apply : EvalBlock (Bits64x2 -> a) -> EvalBlock Bits64x2 -> EvalBlock a
apply = (<$>)

ebmap : (Bits64x2 -> Bits64x2) -> EvalBlock Bits64x2 -> EvalBlock Bits64x2
ebmap = map

partial
evalBlock : (bases : Vect Bits64x2 n) -> (env : Vect Bits64x2 m) -> BitStream n m ty -> evalBlockTy ty
evalBlock bs _ (Basis i) = pure (index i bs)
evalBlock bs env (Lam body) = \v => evalBlock bs (v :: env) body
evalBlock {ty=TyStream} bs env (App f a) = do
  arg <- the (evalBlockTy TyStream) (evalBlock bs env a)
  (the (evalBlockTy (TyFun TyStream)) (evalBlock bs env f)) arg
evalBlock _ env (Ref var) = pure (index var env)
-- evalBlock bs env (Output xs) = sequence (the (List (EvalBlock Bits64x2)) (toList (map (evalBlock bs env) xs)))
  -- let pairs = map (\b => evalBlock cin env b bs) xs in
  -- (concatMap fst (toList pairs), map snd pairs)
evalBlock bs env (Or l r) =
  pure prim__orB64x2
  <$> the (evalBlockTy TyStream) (evalBlock bs env l)
  <$> the (evalBlockTy TyStream) (evalBlock bs env r)
evalBlock bs env (And l r) =
  pure prim__andB64x2
  <$> the (evalBlockTy TyStream) (evalBlock bs env l)
  <$> the (evalBlockTy TyStream) (evalBlock bs env r)
evalBlock bs env (XOr l r) =
  pure prim__xorB64x2
  <$> the (evalBlockTy TyStream) (evalBlock bs env l)
  <$> the (evalBlockTy TyStream) (evalBlock bs env r)
evalBlock bs env (Not b) = ebmap prim__complB64x2 (the (evalBlockTy TyStream) (evalBlock bs env b))
evalBlock bs env (Add ls rs) = do
  carry <- popCarry
  l <- the (evalBlockTy TyStream) (evalBlock bs env ls)
  r <- the (evalBlockTy TyStream) (evalBlock bs env rs)
  let lh = prim__indexB64x2 l 0
  let ll = prim__indexB64x2 l 1
  let rh = prim__indexB64x2 r 0
  let rl = prim__indexB64x2 r 1
  let (c1, ll') = addWithCarry ll carry
  let (c2, lsum) = addWithCarry ll' rl
  let (c3, rh') = addWithCarry rh (c1 + c2)
  let (newCarry, hsum) = addWithCarry lh rh'
  tellCarry newCarry
  pure (prim__mkB64x2 hsum lsum)

partial
test : BitStream 1 0 (TyFun TyStream)
test = bitstream (\x => Add (Add x x) (Basis fO))

partial
test' : Bits64x2 -> (List Bits64, Bits64x2)
test' x = runEval [] ((the (evalBlockTy (TyFun TyStream)) (evalBlock [prim__mkB64x2 42 17] [] Main.test)) x)
