module CSV

import BitStream

escape : BitStream 8 e TyStream
escape = bitstream (
  let odd = bytePattern 0xAA in
  let even = bytePattern 0x55 in
  let backslash = char '\\' in
  let start = backslash .&. Not (backslash .>>. 1) in
  let even_start = start .&. even in
  let even_final = [| scan backslash even_start |] in
  let even_escape = even_final .&. odd in
  let odd_start = start .&. odd in
  let odd_final = [| scan backslash odd_start |] in
  let odd_escape = odd_final .&. even in
  even_escape .|. odd_escape
  )

-- FIXME: Shadows?
quoteParity : BitStream 8 e (TyFun TyStream)
quoteParity = bitstream (
  \quote =>
   let p2 = quote .^. (quote .>>. 1) in
   let p4 = p2 .^. (p2 .>>. 2) in
   let p8 = p4 .^. (p4 .>>. 4) in
   let p16 = p8 .^. (p8 .>>. 8) in
   let p32 = p16 .^. (p16 .>>. 16) in
   let p64 = p32 .^. (p32 .>>. 32) in
   p64 .^. (p64 .>>. 64)
  )

csv : BitStream 8 0 (TyOutput 4)
csv = bitstream (
  let esc = escape in
  let quote = char '\"' .&. Not esc in
  let quoteMask = [| quoteParity quote |] in
  let cr = char '\r' in
  let eol = (cr .&. Not quoteMask) .|. (char '\n' .&. Not cr .&. Not quoteMask) in
  let delim = char ',' .&. Not quoteMask in
  Output [esc, quote, eol, delim]
  )