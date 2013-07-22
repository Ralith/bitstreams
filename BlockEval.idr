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
