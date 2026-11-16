/-! Outward-rounded fixed-point interval arithmetic over `Int`, written for kernel evaluation (core Lean only).
Adapted from the tiny-transformer development (`TinyBayes.Interval`), at scale `2^24 * 3^174` with weights over `2^24`.

An interval `⟨lo, hi, ok⟩` encloses a real `x` at scale `s` when `ok = true → lo ≤ x * s ≤ hi`.
The working scale is `S = 2^24 * 3^174`; products of two intervals live at scale `S * S` until `downBy S`
rounds them back. `ok = false` carries no information: it is how an operation reports that its
side condition failed (a reciprocal of an interval that is not positive, or a too-large `exp`
argument). Soundness of every operation over `ℝ` is proved in `PRO.IntervalSound`. -/

namespace PRO

/-- Fixed-point scale `S = 2^24 * 3^174` (about `2^300`; the odd factor keeps the low bits of the numerals varied). -/
def S : Int := 1753146532884332471079573454801035572631296275562533789850571540248761047936531377216815104

/-- `S / 2^24 = 3^174`. -/
def S76 : Int := 104495676331778315966103878903450701989608781073244439950619431748912396904023371769

/-- Number of squarings in `exp`: `exp x = (exp (x / 2^M))^(2^M)` with `M = 155`. -/
def M : Nat := 155

/-- `2^M`. -/
def TWO_M : Int := 45671926166590716193865151022383844364247891968

/-- `S * 2^M`. -/
def SM : Int := 80069579009107735684535927840422415386330680189185515585582768449133646728589145805856731175328099021224202159399197873892500514822684672

structure Iv where
  lo : Int
  hi : Int
  ok : Bool

/-- `⌊a / b⌋` for `b > 0`. -/
def fdiv (a b : Int) : Int := a / b

/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a b : Int) : Int := -((-a) / b)

def zero : Iv := ⟨0, 0, true⟩

/-- The real `1` at scale `S`. -/
def one : Iv := ⟨S, S, true⟩

def add (X Y : Iv) : Iv := ⟨X.lo + Y.lo, X.hi + Y.hi, X.ok && Y.ok⟩

def neg (X : Iv) : Iv := ⟨-X.hi, -X.lo, X.ok⟩

/-- Product with the integer `w` (exact; same scale). -/
def mulZ (w : Int) (X : Iv) : Iv :=
  if 0 ≤ w then ⟨w * X.lo, w * X.hi, X.ok⟩ else ⟨w * X.hi, w * X.lo, X.ok⟩

/-- Product of two intervals (four corners, exact): scales multiply. -/
def mulRaw (X Y : Iv) : Iv :=
  let a := X.lo * Y.lo
  let b := X.lo * Y.hi
  let c := X.hi * Y.lo
  let d := X.hi * Y.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d), X.ok && Y.ok⟩

/-- Divide the scale by `d > 0`, rounding outward. -/
def downBy (d : Int) (X : Iv) : Iv := ⟨fdiv X.lo d, cdiv X.hi d, X.ok⟩

/-- Product of two intervals at scale `S`. -/
def mul (X Y : Iv) : Iv := downBy S (mulRaw X Y)

/-- Reciprocal of a positive interval. -/
def recip (X : Iv) : Iv := ⟨fdiv (S * S) X.hi, cdiv (S * S) X.lo, X.ok && decide (0 < X.lo)⟩

def relu (X : Iv) : Iv := ⟨max 0 X.lo, max 0 X.hi, X.ok⟩

/-- Square `k` times, rounding down. -/
def sqLo : Nat → Int → Int
  | 0, a => a
  | k + 1, a => sqLo k (fdiv (a * a) S)

/-- Square `k` times, rounding up. -/
def sqHi : Nat → Int → Int
  | 0, a => a
  | k + 1, a => sqHi k (cdiv (a * a) S)

/-- Lower bound for `exp (n / S) * S`: `(max 0 (1 + y))^(2^M)` with `y = n / (S 2^M)`. -/
def expLo (n : Int) : Int := sqLo M (max 0 (S + fdiv n TWO_M))

/-- Upper bound for `exp (n / S) * S` when `n < S 2^M`: `(1 / (1 - y))^(2^M)`. -/
def expHi (n : Int) : Int := sqHi M (cdiv (S * SM) (SM - n))

def expI (X : Iv) : Iv := ⟨expLo X.lo, expHi X.hi, X.ok && decide (X.hi < SM)⟩

/-- The exact weight `z / 2^24` at scale `S`. -/
def ofW (z : Int) : Iv := ⟨z * S76, z * S76, true⟩

def sumI (L : List Iv) : Iv := L.foldr add zero

def vaddI (X Y : List Iv) : List Iv := List.zipWith add X Y

/-- Dot product of a weight row (numerators over 2^24) with an interval vector; one rounding. -/
def dotWI (row : List Int) (X : List Iv) : Iv := downBy 16777216 (sumI (List.zipWith mulZ row X))

/-- Dot product of two interval vectors; one rounding. -/
def dotI (X Y : List Iv) : Iv := downBy S (sumI (List.zipWith mulRaw X Y))

/-- Weight matrix (numerators over 2^24) times an interval vector. -/
def mvI (W : List (List Int)) (X : List Iv) : List Iv := W.map fun row => dotWI row X

end PRO
