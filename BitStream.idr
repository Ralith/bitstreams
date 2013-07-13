module BitStream

data Ty = TyStream
        | TyOutput Nat
        -- | TyFun Ty

data BitStream : (inputWidth : Nat) -> (environmentDepth : Nat) -> (type : Ty) -> Type where
  Basis : Fin n -> BitStream n e TyStream
  Let : BitStream n e TyStream -> BitStream n (S e) t -> BitStream n e t
  -- Lam : BitStream n (S e) t -> BitStream n e (TyFun t)
  -- App : BitStream n e (TyFun t) -> BitStream n e TyStream -> BitStream n e t
  Ref : Fin e -> BitStream n e TyStream
  Output : Vect (BitStream n e TyStream) c -> BitStream n e (TyOutput c)
  Or : BitStream n e TyStream -> BitStream n e TyStream -> BitStream n e TyStream
  And : BitStream n e TyStream -> BitStream n e TyStream -> BitStream n e TyStream
  XOr : BitStream n e TyStream ->  BitStream n e TyStream -> BitStream n e TyStream
  Not : BitStream n e TyStream -> BitStream n e TyStream
  Add : String -> BitStream n e TyStream -> BitStream n e TyStream -> BitStream n e TyStream

dsl bitstream
  let = Let
  variable = Ref
  index_first = fO
  index_next = fS
--  lambda = Lam

-- pure : BitStream n e t -> BitStream n e t
-- pure = id

-- (<$>) : BitStream n e (TyFun t) -> BitStream n e TyStream -> BitStream n e t
-- (<$>) = App

bitAt64 : Bits64 -> Bits64 -> Bool
bitAt64 pos x = 0 /= prim__andB64 x (prim__shlB64 1 pos)

showB64 : Bits64 -> String
showB64 x = helper 64
  where
    helper : Bits64 -> String
    helper 0 = ""
    helper n = (if bitAt64 (n-1) x then "1" else "0") ++ helper (n-1)

showB64x2 : Bits64x2 -> String
showB64x2 v = showB64 (prim__indexB64x2 v 1) ++ showB64 (prim__indexB64x2 v 0)

bitAt : Bits8 -> Bits8 -> Bool
bitAt pos x = 0 /= prim__andB8 x (prim__shlB8 1 pos)

finToB8 : Fin n -> Bits8 -- Should be Fin 256, but a general weaken is too slow
finToB8 fO = 0
finToB8 (fS x) = 1 + finToB8 (weaken x)

basis : Bits8 -> BitStream 8 e TyStream
basis b = helper 7
  where
    helper : Fin 8 -> BitStream 8 e TyStream
    helper fO = if bitAt 0 b then Basis 0 else Not (Basis 0)
    helper (fS x) = And (helper (weaken x)) (if bitAt (finToB8 (fS x)) b then Basis (fS x) else Not (Basis (fS x)))

char : Char -> BitStream 8 e TyStream
char = basis . prim__truncInt_B8 . prim__charToInt

all : Vect (BitStream n e TyStream) (S k) -> BitStream n e TyStream
all [x] = x
all (x::(y::ys)) = And x (all (y::ys))

any : Vect (BitStream n e TyStream) (S k) -> BitStream n e TyStream
any [x] = x
any (x::(y::ys)) = Or x (any (y::ys))

digit : BitStream 8 e TyStream
digit =
  all [ Not (Basis 7)
      , Not (Basis 6)
      , Basis 5
      , Basis 4
      , Or (Not (Basis 3))
           (And (Not (Basis 2))
                (Not (Basis 1)))
      ]

scan : String -> BitStream n e TyStream -> BitStream n e TyStream -> BitStream n e TyStream
scan id fields cursors = And (Not fields) (Add id cursors fields)

interpTyBlock : Ty -> Type
interpTyBlock TyStream = Bits64x2
interpTyBlock (TyOutput n) = Vect Bits64x2 n
--interpTyBlock (TyFun t) = Bits64x2 -> (interpTyBlock t)

boolToB64 : Bool -> Bits64
boolToB64 True = 1
boolToB64 False = 0

addWithCarry : Bits64 -> Bits64 -> (Bits64, Bits64)
addWithCarry l r = (boolToB64 ((18446744073709551615 - r) < l), l + r)

evalBlock : List (String, Bits64) -> Vect Bits64x2 n -> BitStream bases n ty -> Vect Bits64x2 bases
         -> (List (String, Bits64), interpTyBlock ty)
evalBlock cin _ (Basis i) bs = (Nil, index i bs)
evalBlock cin env (Let val body) bs =
  let (carries, valBlock) = evalBlock cin env val bs in
  let (carries', result) = evalBlock cin (valBlock :: env) body bs in
  (carries ++ carries', result)
-- evalBlock cin env (Lam body) bs = \v => evalBlock cin (v :: env) body bs
-- evalBlock cin env (App f a) bs = (evalBlock env f bs) (evalBlock env a bs)
evalBlock cin env (Ref var) _ = (Nil, index var env)
evalBlock cin env (Output xs) bs =
  let pairs = map (\b => evalBlock cin env b bs) xs in
  (concatMap fst (toList pairs), map snd pairs)
evalBlock cin env (Or l r) bs =
  let (carriesl, bl) = evalBlock cin env l bs in
  let (carriesr, br) = evalBlock cin env r bs in
  (carriesl ++ carriesr, bl `prim__orB64x2` br)
evalBlock cin env (And l r) bs =
  let (carriesl, bl) = evalBlock cin env l bs in
  let (carriesr, br) = evalBlock cin env r bs in
  (carriesl ++ carriesr, bl `prim__andB64x2` br)
evalBlock cin env (XOr l r) bs =
  let (carriesl, bl) = evalBlock cin env l bs in
  let (carriesr, br) = evalBlock cin env r bs in
  (carriesl ++ carriesr, bl `prim__xorB64x2` br)
evalBlock cin env (Not b) bs =
  let (carries, b) = evalBlock cin env b bs in
  (carries, prim__complB64x2 b)
evalBlock cin env (Add id ls rs) bs =
  let (carries, l) = evalBlock cin env ls bs in
  let (carries, r) = evalBlock cin env rs bs in
  let lh = prim__indexB64x2 l 0 in
  let ll = prim__indexB64x2 l 1 in
  let rh = prim__indexB64x2 r 0 in
  let rl = prim__indexB64x2 r 1 in
  let (lcarry, lsum) = addWithCarry ll rl in
  let (hcarry, hsum) = addWithCarry lh rh in
  case lookup id cin of
    Just oldCarry =>
      let (lcarry', lsum') = addWithCarry lsum oldCarry in
      let (hcarry', hsum') = addWithCarry hsum (lcarry + lcarry') in
      (((id, hcarry + hcarry')::carries), prim__mkB64x2 hsum' lsum')
    Nothing => (((id, hcarry)::carries), prim__mkB64x2 (hsum + lcarry) lsum)

test : BitStream 1 e (TyOutput 2)
test = bitstream (
  let b0 = Basis 0 in
  Output [Add "a" b0 b0, b0]
  )

intStart : BitStream 8 e (TyOutput 1)
intStart = bitstream (
  let d = digit in
  let nd = Not d in
  Output [scan "a" d nd]
  )

-- csv : BitStream 8 e (TyOutput 0)
-- csv = bitstream (
--   let comma = char ','
--       quote = char '\''
--       dquote = char '\"'
--       lf = char '\n'
--   in 
--   )

-- evalBytes : BitStream 8 O (TyOutput n) -> (s : String) -> List (Vect Bits64x2 n)
-- evalBytes b s = step 0
--   where
--     len : Int
--     len = length s

--     step : Int -> Vect Bits8x16 n
--     step x with (x < len)
--       | False = []
--       | True = let bytes = (min 8 (len - x))
--                 in evalBlock [] b (transpose (loadBytes x bytes))
--                    :: step (x + bytes)

-- loadBytes : Int -> Int -> Bits8x16 -> Bits8x16
-- loadBytes _ 0 v = v
-- loadBytes i r v = prim__updateB8x16 (loadByte i (r-1) v) (prim__truncB64_B32 . prim__zextInt_B64 $ r) (prim__truncInt_B8 . prim__charToInt $ strIndex s (i+r))

-- transpose : Vect Bits8x16 8 -> Vect Bits8x16 8