module Main

import BitStream

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
  Output [scan "a" d (Not d)]
  )

packuswb : Bits16x8 -> Bits16x8 -> Bits8x16
packuswb a b = unsafePerformIO (mkForeign (FFun "llvm.x86.sse2.packuswb.128" [FBits16x8, FBits16x8] FBits8x16) a b)

psrldq : Bits64x2 -> Bits32 -> Bits64x2
psrldq v s = unsafePerformIO (mkForeign (FFun "llvm.x86.sse2.psrl.dq" [FBits64x2, FBits32] FBits64x2) v s)

packh8 : Bits16x8 -> Bits16x8 -> Bits64x2
packh8 a b = prim__bitcastB8x16_B64x2 (packuswb (frob a) (frob b))
  where
    frob : Bits16x8 -> Bits16x8
    frob x = prim__lshrB16x8 x (uniformB16x8 8)

packl8 : Bits16x8 -> Bits16x8 -> Bits64x2
packl8 a b = prim__bitcastB8x16_B64x2 (packuswb (frob a) (frob b))
  where
    frob : Bits16x8 -> Bits16x8
    frob x = prim__andB16x8 x (uniformB16x8 0x00FF)

vsel : Bits64x2 -> Bits64x2 -> Bits64x2 -> Bits64x2
vsel cond then_ else_ =
  prim__orB64x2 (prim__andB64x2 cond then_)
                (prim__andB64x2 (prim__complB64x2 cond) else_)

-- simd_or(simd128<64>::srli<sh>(arg1), _mm_srli_si128(simd128<64>::slli<((128-sh)&63)>(arg1), (int32_t)(8)))));
-- s < 64
lshr128 : Bits64x2 -> Bits8 -> Bits64x2
lshr128 x s = prim__orB64x2 (prim__lshrB64x2 x (toVecShift s))
                            (psrldq (prim__shlB64x2 x (toVecShift ((128 - s) `prim__andB8` 63))) (prim__zextB8_B32 s))
  where
    toVecShift : Bits8 -> Bits64x2
    toVecShift s = uniformB64x2 (prim__zextB8_B64 s)

packl4 : Bits64x2 -> Bits64x2 -> Bits64x2
packl4 a b = packl8 (frob a) (frob b)
  where
    frob : Bits64x2 -> Bits16x8
    frob x = prim__bitcastB64x2_B16x8 (vsel (uniformB64x2 0xCC) (lshr128 x 2) x)

packh4 : Bits64x2 -> Bits64x2 -> Bits64x2
packh4 a b = packl4 (frob a) (frob b)
  where
    frob : Bits64x2 -> Bits64x2
    frob x = prim__lshrB64x2 x (uniformB64x2 2)

packl2 : Bits64x2 -> Bits64x2 -> Bits64x2
packl2 a b = packl4 (frob a) (frob b)
  where
    frob : Bits64x2 -> Bits64x2
    frob x = vsel (uniformB64x2 0xAA) (lshr128 x 1) x

packh2 : Bits64x2 -> Bits64x2 -> Bits64x2
packh2 a b = packl2 (frob a) (frob b)
  where
    frob x = prim__lshrB64x2 x (uniformB64x2 1)

-- lib/s2p.hpp:54 s2p_ideal
transpose : Vect Bits8x16 8 -> Vect Bits64x2 8
transpose xs =
   let a = index fO xs in
   let b = index (fS fO) xs in
   let c = index (fS (fS fO)) xs in
   let d = index (fS (fS (fS fO))) xs in
   let e = index (fS (fS (fS (fS fO)))) xs in
   let f = index (fS (fS (fS (fS (fS fO))))) xs in
   let g = index (fS (fS (fS (fS (fS (fS fO)))))) xs in
   let h = index (fS (fS (fS (fS (fS (fS (fS fO))))))) xs in
   let bit0123_0 = packh8' a b in
   let bit0123_1 = packh8' c d in
   let bit0123_2 = packh8' e f in
   let bit0123_3 = packh8' g h in
   let bit4567_0 = packl8' a b in
   let bit4567_1 = packl8' c d in
   let bit4567_2 = packl8' e f in
   let bit4567_3 = packl8' g h in
   let bit01_0 = packh4 bit0123_0 bit0123_1 in
   let bit01_1 = packh4 bit0123_2 bit0123_3 in
   let bit23_0 = packl4 bit0123_0 bit0123_1 in
   let bit23_1 = packl4 bit0123_2 bit0123_3 in
   let bit45_0 = packh4 bit4567_0 bit4567_1 in
   let bit45_1 = packh4 bit4567_2 bit4567_3 in
   let bit67_0 = packl4 bit4567_0 bit4567_1 in
   let bit67_1 = packl4 bit4567_2 bit4567_3 in
   [ packh2 bit01_0 bit01_1, packl2 bit01_0 bit01_1
   , packh2 bit23_0 bit23_1, packl2 bit23_0 bit23_1
   , packh2 bit45_0 bit45_1, packl2 bit45_0 bit45_1
   , packh2 bit67_0 bit67_1, packl2 bit67_0 bit67_1
   ]
  where
    packh8' : Bits8x16 -> Bits8x16 -> Bits64x2
    packh8' x y = packh8 (prim__bitcastB8x16_B16x8 x) (prim__bitcastB8x16_B16x8 y)
    packl8' : Bits8x16 -> Bits8x16 -> Bits64x2
    packl8' x y = packh8 (prim__bitcastB8x16_B16x8 x) (prim__bitcastB8x16_B16x8 y)

ApplyTy : Type -> Type -> Nat -> Type
ApplyTy r _ O = r
ApplyTy r a (S k) = a -> ApplyTy r a k

apply : (ApplyTy a b n) -> Vect b n -> a
apply {n=O}   x [] = x
apply {n=S _} f (x::xs) = apply (f x) xs

packBytes : String -> Vect Bits8x16 8
packBytes xs = map take16 [0,1,2,3,4,5,6,7]
  where
    b : Int -> Bits8
    b x = prim__truncInt_B8 (prim__charToInt (prim__strIndex xs x))

    take16 : Int -> Bits8x16
    take16 off = apply prim__mkB8x16 (map (b . ((16*off)+)) [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])

ipsum : String
ipsum = "Lorem ipsum dolor sit amet, consectetur adipisicing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."

main : IO ()
main = print . transpose . packBytes $ ipsum
