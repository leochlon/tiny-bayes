/-! Decoding IEEE 754 half-precision bit patterns (core Lean only).

A finite float16 with bit pattern `b` (sign bit 15, exponent bits 10..14, fraction bits 0..9) is the
rational `f16num b / 2^24`: for exponent field `e ≥ 1` it is `± (1024 + f) * 2^(e - 25)`, and for
`e = 0` (subnormal or zero) it is `± f * 2^(-24)`. No parameter of pythia-14m has `e = 31`. -/

namespace CON

/-- Numerator over `2^24` of the float16 with bit pattern `b`. -/
def f16num (b : Nat) : Int :=
  let e := (b / 1024) % 32
  let f := b % 1024
  let mag : Nat := if e = 0 then f else (1024 + f) * 2 ^ (e - 1)
  if (b / 32768) % 2 = 1 then -(mag : Int) else (mag : Int)

/-- Entry `j` of a packed row: bits `[16 j, 16 j + 16)`. -/
def field (r j : Nat) : Nat := (r >>> (16 * j)) % 65536

end CON
