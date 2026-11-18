import Mathlib.Data.Int.Basic

namespace PinnCert

/-- Fixed-point scale `S = 2^64`. -/
def S : Int := 18446744073709551616

/-- Number of squarings in `exp`. -/
def M : Nat := 32

/-- `2^M`. -/
def TWO_M : Int := 4294967296

/-- `S * 2^M`. -/
def SM : Int := 79228162514264337593543950336

structure Iv where
  lo : Int
  hi : Int
  ok : Bool

def fdiv (a b : Int) : Int := a / b

def cdiv (a b : Int) : Int := -((-a) / b)

def zero : Iv := ⟨0, 0, true⟩

def one : Iv := ⟨S, S, true⟩

def cst (a : Int) : Iv := ⟨a, a, true⟩

def add (X Y : Iv) : Iv := ⟨X.lo + Y.lo, X.hi + Y.hi, X.ok && Y.ok⟩

def neg (X : Iv) : Iv := ⟨-X.hi, -X.lo, X.ok⟩

def mulZ (w : Int) (X : Iv) : Iv :=
  if 0 ≤ w then ⟨w * X.lo, w * X.hi, X.ok⟩ else ⟨w * X.hi, w * X.lo, X.ok⟩

def mulRaw (X Y : Iv) : Iv :=
  let a := X.lo * Y.lo
  let b := X.lo * Y.hi
  let c := X.hi * Y.lo
  let d := X.hi * Y.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d), X.ok && Y.ok⟩

def downBy (d : Int) (X : Iv) : Iv := ⟨fdiv X.lo d, cdiv X.hi d, X.ok⟩

def mul (X Y : Iv) : Iv := downBy S (mulRaw X Y)

/-- Enclosure of `x ^ 2` at the squared scale. -/
def sqRaw (X : Iv) : Iv :=
  let a := X.lo * X.lo
  let b := X.hi * X.hi
  ⟨if 0 ≤ X.lo then a else if X.hi ≤ 0 then b else 0, max a b, X.ok⟩

/-- Enclosure of `1 - x ^ 2`. -/
def omsq (X : Iv) : Iv := add one (neg (downBy S (sqRaw X)))

def sqLo : Nat → Int → Int
  | 0, a => a
  | k + 1, a => sqLo k (fdiv (a * a) S)

def sqHi : Nat → Int → Int
  | 0, a => a
  | k + 1, a => sqHi k (cdiv (a * a) S)

def expLo (n : Int) : Int := sqLo M (max 0 (S + fdiv n TWO_M))

def expHi (n : Int) : Int := sqHi M (cdiv (S * SM) (SM - n))

def expI (X : Iv) : Iv := ⟨expLo X.lo, expHi X.hi, X.ok && decide (X.hi < SM)⟩

/-- `tanh x = 1 - 2 / (exp (2 x) + 1)`, monotone in `exp (2 x)`. -/
def tanhI (X : Iv) : Iv :=
  let El := expLo (2 * X.lo)
  let Eh := expHi (2 * X.hi)
  ⟨S - cdiv (2 * S * S) (El + S), S - fdiv (2 * S * S) (Eh + S), X.ok && decide (2 * X.hi < SM)⟩


end PinnCert
