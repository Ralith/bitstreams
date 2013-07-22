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

test : BitStream 1 e (TyOutput 2)
test = bitstream (
  let b0 = Basis 0 in
  Output [Add "a" b0 b0, b0]
  )

intStart : BitStream 8 e (TyOutput 1)
intStart = bitstream (
  let d = digit in
  Output [scan "a" d (Not d)]
  )
