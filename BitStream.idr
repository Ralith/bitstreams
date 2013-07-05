module BitStream

data Ty = TyStream
        | TyOutput Nat
--        | TyFun Ty

data BitStream : (inputWidth : Nat) -> (environmentDepth : Nat) -> (carries : Nat) -> (type : Ty) -> Type where
  Basis : Fin n -> BitStream n e O TyStream
  Let : BitStream n e c1 TyStream -> BitStream n (S e) c2 t -> BitStream n e (c1 + c2) t
  -- Lam : BitStream n (S e) c t -> BitStream n e c (TyFun t)
  -- App : BitStream n e (TyFun t) -> BitStream n e TyStream -> BitStream n e t
  Ref : Fin e -> BitStream n e O TyStream
  Output : (bs : Vect (cr ** BitStream n e cr TyStream) oc) -> BitStream n e (sumCarries bs) (TyOutput oc)
  Or : BitStream n e c1 TyStream -> BitStream n e c2 TyStream -> BitStream n e (c1 + c2) TyStream
  And : BitStream n e c1 TyStream -> BitStream n e c2 TyStream -> BitStream n e (c1 + c2) TyStream
  XOr : BitStream n e c1 TyStream ->  BitStream n e c2 TyStream -> BitStream n e (c1 + c2) TyStream
  Not : BitStream n e c TyStream -> BitStream n e c TyStream
  Add : BitStream n e c1 TyStream -> BitStream n e c2 TyStream -> BitStream n e (S (c1 + c2)) TyStream

sumCarries : Vect (c ** BitStream n e c t) k -> Nat
sumCarries [] = O
sumCarries ((c ** _) :: xs) = c + sumCarries xs

dsl bitstream
  let = Let
  variable = Ref
  index_first = fO
  index_next = fS
--  lambda = Lam

-- pure : BitStream n e c t -> BitStream n e c t
-- pure = id

-- (<$>) : BitStream n e c (TyFun t) -> BitStream n e c TyStream -> BitStream n e c t
-- (<$>) = App

instance Num Bits8 where
  (+) = prim__addB8
  (-) = prim__subB8
  (*) = prim__mulB8
  abs = id
  fromInteger = prim__truncBigInt_B8

instance Num Bits32 where
  (+) = prim__addB32
  (-) = prim__subB32
  (*) = prim__mulB32
  abs = id
  fromInteger = prim__truncBigInt_B32

instance Num Bits64 where
  (+) = prim__addB64
  (-) = prim__subB64
  (*) = prim__mulB64
  abs = id
  fromInteger = prim__truncBigInt_B64

instance Eq Bits8 where
  x == y = intToBool (prim__eqB8 x y)

bitAt : Bits8 -> Bits8 -> Bool
bitAt pos x = 0 /= prim__andB8 x (prim__shlB8 1 pos)

finToB8 : Fin n -> Bits8 -- Should be Fin 256, but a general weaken is too slow
finToB8 fO = 0
finToB8 (fS x) = 1 + finToB8 (weaken x)

basis : Bits8 -> BitStream 8 e O TyStream
basis b = helper 7
  where
    helper : Fin 8 -> BitStream 8 e O TyStream
    helper fO = if bitAt 0 b then Basis 0 else Not (Basis 0)
    helper (fS x) = And (helper (weaken x)) (if bitAt (finToB8 (fS x)) b then Basis (fS x) else Not (Basis (fS x)))

char : Char -> BitStream 8 e c TyStream
char = basis . prim__truncInt_B8 . prim__charToInt

all : (bs : Vect (c ** BitStream n e c TyStream) (S k)) -> BitStream n e (sumCarries bs) TyStream
all [x] = x
all (x::(y::ys)) = And x (all (y::ys))

any : (bs : Vect (c ** BitStream n e TyStream) (S k)) -> BitStream n e (sumCarries bs) TyStream
any [x] = x
any (x::(y::ys)) = Or x (any (y::ys))

digit : BitStream 8 e TyStream
digit =
  all [ (_ ** Not (Basis 7))
      , (_ ** Not (Basis 6))
      , (_ ** Basis 5)
      , (_ ** Basis 4)
      , (_ ** Or (Not (Basis 3))
                 (And (Not (Basis 2))
                      (Not (Basis 1))))
      ]

scan : BitStream n e TyStream -> BitStream n e TyStream -> BitStream n e TyStream
scan fields cursors = And (Not fields) (Add cursors fields)

interpTyBlock : Ty -> Type
interpTyBlock TyStream = Bits64x2
interpTyBlock (TyOutput n) = Vect Bits64x2 n
interpTyBlock (TyFun t) = Bits64x2 -> (interpTyBlock t)

addWithCarry : Bits64 -> Bits64 -> (Bits64, Bits64)
addWithCarry l r = (prim__zextInt_B64 ((18446744073709551615 - r) `prim__ltB64` l), l + r)

evalBlock : Vect Bits64x2 n -> BitStream bases n ty -> Vect Bits64x2 bases -> interpTyBlock ty
evalBlock _ (Basis i) bs = index i bs
evalBlock env (Let val body) bs = evalBlock (evalBlock env val bs :: env) body bs
--evalBlock env (Lam body) bs = \v => evalBlock (v :: env) body bs
--evalBlock env (App f a) bs = (evalBlock env f bs) (evalBlock env a bs)
evalBlock env (Ref var) _ = index var env
evalBlock env (Output xs) bs = map (\b => evalBlock env b bs) xs
evalBlock env (Or l r) bs = evalBlock env l bs `prim__orB64x2` evalBlock env r bs
evalBlock env (And l r) bs = evalBlock env l bs `prim__andB64x2` evalBlock env r bs
evalBlock env (XOr l r) bs = evalBlock env l bs `prim__xorB64x2` evalBlock env r bs
evalBlock env (Not b) bs = prim__complB64x2 (evalBlock env b bs)
evalBlock env (Add ls rs) bs =
  let l = evalBlock env ls bs in
  let r = evalBlock env rs bs in
  let lh = prim__indexB64x2 l 0 in
  let ll = prim__indexB64x2 l 1 in
  let rh = prim__indexB64x2 r 0 in
  let rl = prim__indexB64x2 r 1 in
  let (hsum, hcarry) = addWithCarry lh rh in
  let (lsum, lcarry) = addWithCarry ll rl in
  prim__mkB64x2 (hsum + lcarry) lsum

test : BitStream 1 e (TyOutput 2)
test = bitstream (
  let b0 = Basis 0 in
  Output [b0, Not b0]
  )

-- csv : BitStream 8 e (TyOutput 0)
-- csv = bitstream (
--   let comma = char ','
--       quote = char '\''
--       dquote = char '\"'
--       lf = char '\n'
--   in 
--   )

-- evalBytes : BitStream 8 O (TyOutput n) -> (s : String) -> List (Vect Bits8x16 n)
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