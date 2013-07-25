module Main

import BitStream
import BlockEval

%default total

packuswb : Bits16x8 -> Bits16x8 -> Bits8x16
packuswb a b = unsafePerformIO (mkForeign (FFun "llvm.x86.sse2.packuswb.128" [FBits16x8, FBits16x8] FBits8x16) a b)

packh16 : Bits64x2 -> Bits64x2 -> Bits64x2
packh16 a b = prim__bitcastB8x16_B64x2 (packuswb (frob a) (frob b))
  where
    frob : Bits64x2 -> Bits16x8
    frob x = prim__lshrB16x8 (prim__bitcastB64x2_B16x8 x) (uniformB16x8 8)

packl16 : Bits64x2 -> Bits64x2 -> Bits64x2
packl16 a b = prim__bitcastB8x16_B64x2 (packuswb (frob a) (frob b))
  where
    frob : Bits64x2 -> Bits16x8
    frob x = prim__andB16x8 (prim__bitcastB64x2_B16x8 x) (uniformB16x8 0x00FF)

vsel : Bits64x2 -> Bits64x2 -> Bits64x2 -> Bits64x2
vsel cond then_ else_ =
  prim__orB64x2 (prim__andB64x2 cond then_)
                (prim__andB64x2 (prim__complB64x2 cond) else_)

%assert_total
flipB64x2 : Bits64x2 -> Bits64x2
flipB64x2 v = prim__mkB64x2 (prim__indexB64x2 v 1) (prim__indexB64x2 v 0)

transpose : Vect Bits8x16 8 -> Vect Bits64x2 8
transpose xs =
   let s0 = get 0 in
   let s1 = get 1 in
   let s2 = get 2 in
   let s3 = get 3 in
   let s4 = get 4 in
   let s5 = get 5 in
   let s6 = get 6 in
   let s7 = get 7 in
   let (b0246_0, b1357_0) = step s0 s1 (uniformB64x2 0xAAAAAAAAAAAAAAAA) 1 in
   let (b0246_1, b1357_1) = step s2 s3 (uniformB64x2 0xAAAAAAAAAAAAAAAA) 1 in
   let (b0246_2, b1357_2) = step s4 s5 (uniformB64x2 0xAAAAAAAAAAAAAAAA) 1 in
   let (b0246_3, b1357_3) = step s6 s7 (uniformB64x2 0xAAAAAAAAAAAAAAAA) 1 in
   let (b04_0, b26_0) = step b0246_0 b0246_1 (uniformB64x2 0xCCCCCCCCCCCCCCCC) 2 in
   let (b04_1, b26_1) = step b0246_2 b0246_3 (uniformB64x2 0xCCCCCCCCCCCCCCCC) 2 in
   let (b15_0, b37_0) = step b1357_0 b1357_1 (uniformB64x2 0xCCCCCCCCCCCCCCCC) 2 in
   let (b15_1, b37_1) = step b1357_2 b1357_3 (uniformB64x2 0xCCCCCCCCCCCCCCCC) 2 in
   let (p0, p4) = step b04_0 b04_1 (uniformB64x2 0xF0F0F0F0F0F0F0F0) 4 in
   let (p1, p5) = step b15_0 b15_1 (uniformB64x2 0xF0F0F0F0F0F0F0F0) 4 in
   let (p2, p6) = step b26_0 b26_1 (uniformB64x2 0xF0F0F0F0F0F0F0F0) 4 in
   let (p3, p7) = step b37_0 b37_1 (uniformB64x2 0xF0F0F0F0F0F0F0F0) 4 in
   map flipB64x2 [p7, p6, p5, p4, p3, p2, p1, p0] -- TODO: Why is the flip needed?
  where
    get : Fin 8 -> Bits64x2
    get i = prim__bitcastB8x16_B64x2 (index i xs)

    step : Bits64x2 -> Bits64x2 -> Bits64x2 -> Bits16 -> (Bits64x2, Bits64x2)
    step s0 s1 himask shift =
      let t0 = packh16 s0 s1 in
      let t1 = packl16 s0 s1 in
      ( vsel himask t0 (prim__bitcastB16x8_B64x2 (prim__lshrB16x8 (prim__bitcastB64x2_B16x8 t1) (uniformB16x8 shift)))
      , vsel himask (prim__bitcastB16x8_B64x2 (prim__shlB16x8 (prim__bitcastB64x2_B16x8 t0) (uniformB16x8 shift))) t1
      )

ApplyTy : Type -> Type -> Nat -> Type
ApplyTy r _ O = r
ApplyTy r a (S k) = a -> ApplyTy r a k

apply : (ApplyTy a b n) -> Vect b n -> a
apply {n=O}   x [] = x
apply {n=S _} f (x::xs) = apply (f x) xs

partial -- TODO: Should reduce to memcpy
packBytes : Int -> String -> Vect Bits8x16 8
packBytes start xs = map take16 [0,1,2,3,4,5,6,7]
  where
    partial
    b : Int -> Bits8
    b x = prim__truncInt_B8 (prim__charToInt (prim__strIndex xs x))

    partial
    take16 : Int -> Bits8x16
    take16 off = apply prim__mkB8x16 (map (b . ((16*off+start)+)) [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])

ipsum : String
ipsum = "Lorem ipsum dolor sit amet, consectetur adipisicing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."

forble : String
forble = "22:17:49 < Ralith> winterwyn: you can now operate on those 128 characters simultaneously with a single instruction :D 22:17:53 < winterwyn> I'm sure that was readily apparent to one skilled in the art 42"

mapIO : (a -> IO ()) -> Vect a n -> IO ()
mapIO _ [] = pure ()
mapIO f (x::xs) = do
  f x
  mapIO f xs

mapIO' : (a -> IO ()) -> List a -> IO ()
mapIO' _ [] = pure ()
mapIO' f (x::xs) = do
  f x
  mapIO' f xs

partial
getByte : String -> Int -> Bits8
getByte str idx = prim__truncInt_B8 (prim__charToInt (prim__strIndex str idx))

%assert_total
parseString : {static} BitStream 8 0 (TyOutput n) -> String -> List (Vect Bits64x2 n)
parseString {n=n} bs str = if rem /= 0 then parseString bs (str `Builtins.(++)` pack (replicate (fromInteger (prim__zextInt_BigInt (128 - rem))) ' ')) -- TODO: Pad with \0
                           else helper 0 []
  where
    len : Int
    len = prim_lenString str

    %assert_total
    rem : Int
    rem = prim__sremInt len 128

    %assert_total
    helper : Int -> List Bits64 -> List (Vect Bits64x2 n)
    helper offset carriesIn =
      let (carriesOut, outputs) = runEval carriesIn (evalBlock (transpose (packBytes offset str)) [] bs) in
      if offset /= len - 128 then outputs :: (helper (offset + 128) carriesOut)
      else [outputs]

passthrough : BitStream 8 0 (TyOutput 10)
passthrough = Output [Basis 7, Basis 6, Basis 5, Basis 4, Basis 3, Basis 2, Basis 1, Basis 0, Add (Basis 0) (Basis 1), Advance 4 (Basis 0)]

partial
main : IO ()
main = do
  mapIO' (\out => do { mapIO (putStrLn . prim__strRev . showB128) out; putStrLn ""; }) (parseString passthrough (pack (replicate 300 '\255')))
