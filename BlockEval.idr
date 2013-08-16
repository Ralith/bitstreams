module BlockEval

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

pure : a -> EvalBlock a
pure = Prelude.Applicative.pure

instance Monad EvalBlock where
  (EB x) >>= f = EB (\cs => let (nc, x', cs') = x cs in
                            let EB g = f x' in
                            let (nc', r, cs'') = g cs' in
                            (nc ++ nc', r, cs''))

(>>=) : EvalBlock a -> (a -> EvalBlock b) -> EvalBlock b
(>>=) x f = Prelude.Monad.(>>=) x f

bind : EvalBlock a -> (a -> EvalBlock b) -> EvalBlock b
bind x f = Prelude.Monad.(>>=) x f

abind : EvalBlock a -> EvalBlock b -> EvalBlock b
abind x y = Prelude.Monad.(>>=) x (\_ => y)

popCarry : EvalBlock Bits64
popCarry = EB (\cs => ([], fromMaybe 0 (head' cs), fromMaybe [] (tail' cs)))

tellCarry : Bits64 -> EvalBlock ()
tellCarry c = EB (\cs => ([c], (), cs))

mutual
  evalBlockTy' : Ty -> Type
  evalBlockTy' TyStream = Bits64x2
  evalBlockTy' (TyOutput n) = Vect n Bits64x2
  evalBlockTy' (TyFun t) = Bits64x2 -> evalBlockTy t

  evalBlockTy : Ty -> Type
  evalBlockTy t = EvalBlock (evalBlockTy' t)

boolToB64 : Bool -> Bits64
boolToB64 True = 1
boolToB64 False = 0

addWithCarry : Bits64 -> Bits64 -> (Bits64, Bits64)
addWithCarry l r = (boolToB64 ((18446744073709551615 - r) < l), l + r)

%assert_total
addWithCarry128 : Bits64 -> Bits64x2 -> Bits64x2 -> (Bits64, Bits64x2)
addWithCarry128 carry l r =
  let lh = prim__indexB64x2 l 0 in
  let ll = prim__indexB64x2 l 1 in
  let rh = prim__indexB64x2 r 0 in
  let rl = prim__indexB64x2 r 1 in
  let (c1, rl') = addWithCarry rl carry in
  let (c2, lsum) = addWithCarry ll rl' in
  let (c3, rh') = addWithCarry rh (c1 + c2) in
  let (newCarry, hsum) = addWithCarry lh rh' in
  (newCarry + c3, prim__mkB64x2 hsum lsum)

mapEB : (a -> EvalBlock b) -> Vect n a -> EvalBlock (Vect n b)
mapEB f xs = sequence (map f xs)

%assert_total
evalBlock : (bases : Vect n Bits64x2) -> (env : Vect m Bits64x2) -> {static} BitStream n m ty -> evalBlockTy ty
evalBlock _ _ (Pattern x) = pure x
evalBlock bs _ (Basis i) = pure (index i bs)
evalBlock {ty=TyFun rty} bs env (Lam body) = pure (\v => evalBlock bs (v :: env) body)
evalBlock bs env (App f x) = do
  arg <- evalBlock bs env x
  fn <- evalBlock bs env f
  fn arg
evalBlock _ env (Ref var) = pure (index var env)
evalBlock {n=n} {m=m} bs env (Output xs) =
  mapEB (evalBlock bs env) xs
evalBlock bs env (Or l r) = [| prim__orB64x2 (evalBlock bs env l) (evalBlock bs env r) |]
evalBlock bs env (And l r) = [| prim__andB64x2 (evalBlock bs env l) (evalBlock bs env r) |]
evalBlock bs env (XOr l r) = [| prim__xorB64x2 (evalBlock bs env l) (evalBlock bs env r) |]
evalBlock bs env (Not b) = [| prim__complB64x2 (evalBlock bs env b) |]
evalBlock bs env (Add ls rs) = do
  carryIn <- popCarry
  l <- evalBlock bs env ls
  r <- evalBlock bs env rs
  let (carry, result) = addWithCarry128 carryIn l r
  tellCarry carry
  pure result
evalBlock bs env (Sub ls rs) = do -- TODO: Borrow propagation
  l <- evalBlock bs env ls
  r <- evalBlock bs env rs
  pure (prim__subB64x2 l r)
evalBlock bs env (Advance shift s) = do
  carryIn <- popCarry
  block <- evalBlock bs env s
  if shift == 64
    then do tellCarry (prim__indexB64x2 block 0)
            pure (prim__mkB64x2 (prim__indexB64x2 block 1) carryIn)
    else do let backshift = 64 - shift
            tellCarry (prim__lshrB64 (prim__indexB64x2 block 0) backshift)
            let a = prim__shlB64x2 block (uniformB64x2 shift)
            pure (prim__mkB64x2 (prim__orB64 (prim__indexB64x2 a 0) (prim__lshrB64 (prim__indexB64x2 block 1) backshift))
                                (prim__orB64 (prim__indexB64x2 a 1) carryIn))

test : BitStream 2 0 (TyFun TyStream)
test = bitstream (\x => Advance 64 x)

partial
test' : Bits64x2 -> (List Bits64, Bits64x2)
test' x = runEval [] (do fn <- evalBlock [uniformB64x2 (pow 2 128 - 1), uniformB64x2 0] [] BlockEval.test
                         fn x)
