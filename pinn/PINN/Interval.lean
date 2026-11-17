import PINN.Wts

/-! Outward-rounded fixed-point interval arithmetic over `Int` for kernel evaluation (core Lean only).

An interval `⟨lo, hi, ok⟩` encloses a real `x` at scale `s` when `ok = true → lo ≤ x * s ≤ hi`.
The working scale is `S = 2^64`; `ok = false` carries no information. Soundness over `ℝ` is in
`PINN.SoundBase` and `PINN.Sound`. -/

namespace PINN

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

def sumI (L : List Iv) : Iv := L.foldr add zero

/-- `Σ (ws_i / 2^16) x_i`. -/
def dotWI (ws : List Int) (X : List Iv) : Iv := downBy 65536 (sumI (List.zipWith mulZ ws X))

/-- `w1 t + b1` for one first-layer unit (weights over `2^16`). -/
def z1I (c b : Int) (T : Iv) : Iv := downBy 65536 (add (mulZ c T) (cst (b * S)))

/-- The time `[p, q] / 2^20` at scale `S`. -/
def tI (p q : Int) : Iv := ⟨p * 17592186044416, q * 17592186044416, true⟩

def layer1 (P : Wts) (T : Iv) : List Iv := List.zipWith (fun c b => tanhI (z1I c b T)) P.w1 P.c1

def layer2 (P : Wts) (A1 : List Iv) : List Iv :=
  List.zipWith (fun row b => add (dotWI row A1) (cst (b * 281474976710656))) P.w2 P.c2

/-- Enclosure of `x ^ 2` at scale `S`. -/
def sqI (X : Iv) : Iv := downBy S (sqRaw X)

/-- Enclosures of a network's value, first and second derivative. -/
structure NV where
  v : Iv
  d : Iv
  d2 : Iv

/-- First-layer derivative terms `W1[i] (1 - a_i^2)`, `a_i = tanh (z1 i)`. -/
def vList (P : Wts) (A1 : List Iv) : List Iv :=
  List.zipWith (fun c s => downBy 65536 (mulZ c s)) P.w1 (A1.map omsq)

/-- `W1[i]^2 a_i (1 - a_i^2)`. -/
def qList (P : Wts) (A1 : List Iv) : List Iv :=
  List.zipWith (fun c x => downBy 65536 (mulZ c (downBy 65536 (mulZ c x)))) P.w1 (List.zipWith mul A1 (A1.map omsq))

/-- `(1 - b_j^2) (D2_j + b_j D_j^2)`, `b_j = tanh (z2 j)`. -/
def d2List (A2 D D2 : List Iv) : List Iv :=
  List.zipWith mul (A2.map omsq) (List.zipWith add D2 (List.zipWith (fun a x => mul a (sqI x)) A2 D))

/-- One pass through the network: `v` encloses `net`, `d` encloses `net'`, `d2` encloses `net''`, with
`tanh' = 1 - tanh^2` and `(1 - tanh^2)' = -2 tanh (1 - tanh^2)`. -/
def netAll (P : Wts) (T : Iv) : NV :=
  let A1 := layer1 P T
  let A2 := (layer2 P A1).map tanhI
  let D := P.w2.map (fun row => dotWI row (vList P A1))
  let D2 := P.w2.map (fun row => dotWI row (qList P A1))
  ⟨add (dotWI P.w3 A2) (cst (P.c3 * 281474976710656)),
   dotWI P.w3 (List.zipWith mul (A2.map omsq) D),
   mulZ (-2) (dotWI P.w3 (d2List A2 D D2))⟩

/-- Enclosure of `e^{-t}`. -/
def emI (T : Iv) : Iv := expI (neg T)

/-- Residual of `N`: `N' + N - e^{-t}`. -/
def rNI (T : Iv) : Iv :=
  let X := netAll WN T
  add (add X.d X.v) (neg (emI T))

/-- Derivative of the residual of `N`: `N'' + N' + e^{-t}`. -/
def rdNI (T : Iv) : Iv :=
  let X := netAll WN T
  add (add X.d2 X.d) (emI T)

/-- Residual of `û = 1 + t Ñ`: `(Ñ + t Ñ') + (1 + t Ñ) - e^{-t}`. -/
def rHI (T : Iv) : Iv :=
  let X := netAll WH T
  add (add (add X.v (mul T X.d)) (add one (mul T X.v))) (neg (emI T))

/-- Derivative of the residual of `û`: `(2 Ñ' + t Ñ'') + (Ñ + t Ñ') + e^{-t}`. -/
def rdHI (T : Iv) : Iv :=
  let X := netAll WH T
  add (add (add (mulZ 2 X.d) (mul T X.d2)) (add X.v (mul T X.d))) (emI T)

/-- A piece `(a, b, lo, hi)`: times `[a / 2^20, b / 2^20]`, residual bounds `[lo / S, hi / S]`. -/
abbrev Piece := Int × Int × Int × Int

/-- `lo ≤ r ≤ hi` on `[a, b] / 2^20`: the enclosure `X` of `r` at `c / 2^20`, widened by `K * |t - c|`, where
`K / S` bounds `|r'|` on the piece (mean value theorem). -/
def okR2 (lo hi a b c : Int) (X D : Iv) : Bool :=
  let K := max (-D.lo) D.hi
  let h := max (c - a) (b - c)
  X.ok && D.ok && decide (a ≤ c) && decide (c ≤ b) &&
    decide (lo * 1048576 ≤ X.lo * 1048576 - K * h) && decide (X.hi * 1048576 + K * h ≤ hi * 1048576)

/-- The piece check for a residual enclosure `R` and its derivative's enclosure `R'`, anchored at the midpoint. -/
def okR (R R' : Iv → Iv) (x : Piece) : Bool :=
  okR2 x.2.2.1 x.2.2.2 x.1 x.2.1 ((x.1 + x.2.1) / 2) (R (tI ((x.1 + x.2.1) / 2) ((x.1 + x.2.1) / 2)))
    (R' (tI x.1 x.2.1))

/-- Piece check for `N`. -/
def okRN (x : Piece) : Bool := okR rNI rdNI x

/-- Piece check for `û`. -/
def okRH (x : Piece) : Bool := okR rHI rdHI x

/-- The pieces start at `a`, each ends where the next starts, `a < b`, `lo ≤ hi`, and the last ends at `4 * 2^20`. -/
def chainOK : Int → List Piece → Bool
  | a, [] => decide (a = 4194304)
  | a, x :: L => decide (x.1 = a) && decide (x.1 < x.2.1) && decide (x.2.2.1 ≤ x.2.2.2) && chainOK x.2.1 L

/-- At a partition point `a`, with `G ∋ g`, `H ∋ h`, `E ∋ e^a` (so `E.lo / S ≤ e^a`): `e^{-a} g ≤ num / 10000` and
`-num / 10000 ≤ e^{-a} h`. -/
def okPt (num : Int) (G H E : Iv) : Bool :=
  G.ok && H.ok && E.ok && decide (10000 * G.hi ≤ num * E.lo) && decide (-(num * E.lo) ≤ 10000 * H.lo)

/-- The pass over the partition points: `g ← g - lo (e^b - e^a)`, `h ← h - hi (e^b - e^a)` on each piece. -/
def seqOK (num : Int) : Iv → Iv → Iv → List Piece → Bool
  | G, H, E, [] => okPt num G H E
  | G, H, E, x :: L =>
    okPt num G H E &&
      (let E' := expI (tI x.2.1 x.2.1)
       let dE := add E' (neg E)
       seqOK num (add G (neg (mul (cst x.2.2.1) dE))) (add H (neg (mul (cst x.2.2.2) dE))) E' L)

/-- Enclosure of `1 - N 0`. -/
def gN0 : Iv := add one (neg (netAll WN (tI 0 0)).v)

end PINN
