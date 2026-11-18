import Mathlib
import CON.Model
import CON.Invariance
import CON.Pythia
import CON.Gauss

/-! # Certified evaluation of pythia-14m on a one-token prompt

Outward-rounded fixed-point interval arithmetic over `Int` (the scheme of the tiny development, at the
scale `S = 2^24 * 3^111`), proved sound over `ℝ`, with a square root, LayerNorm, the Gaussian integral
(`CON.Gauss`), GELU, and the one-token forward pass `stepCI` of a layer given by its packed float16 rows.
`pred1_encl` turns eighteen kernel-checked steps (three per layer) and one final check into an enclosure of
the candidate-renormalised prediction of `pythia14m` after a one-token prompt. -/

namespace CON



/-- Fixed-point scale `S = 2^24 * 3^111` (the odd factor keeps the low bits of the numerals varied). -/
def S : Int := 1531719247873250720634220761394392004585863364423008494026752

/-- `S / 2^24 = 3^111`. -/
def S88 : Int := 91297581665113611259115979754590511595360241199911147

/-- Number of squarings in `exp`: `exp x = (exp (x / 2^M))^(2^M)` with `M = 100`. -/
def M : Nat := 100

/-- `2^M`. -/
def TWO_M : Int := 1267650600228229401496703205376

/-- `S * 2^M`. -/
def SM : Int := 1941684823947658367165494724761983909631197813215268003976680952586113606683914267894218752

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

/-- The exact weight `z / 16777216` at scale `S`. -/
def ofW (z : Int) : Iv := ⟨z * S88, z * S88, true⟩

def sumI (L : List Iv) : Iv := L.foldr add zero

def vaddI (X Y : List Iv) : List Iv := List.zipWith add X Y

/-- Dot product of a weight row (numerators over 16777216) with an interval vector; one rounding. -/
def dotWI (row : List Int) (X : List Iv) : Iv := downBy 16777216 (sumI (List.zipWith mulZ row X))

/-- Dot product of two interval vectors; one rounding. -/
def dotI (X Y : List Iv) : Iv := downBy S (sumI (List.zipWith mulRaw X Y))

/-- Weight matrix (numerators over 16777216) times an interval vector. -/
def mvI (W : List (List Int)) (X : List Iv) : List Iv := W.map fun row => dotWI row X





/-- `X` encloses `x` at scale `s`. -/
def memAt (s x : ℝ) (X : Iv) : Prop := X.ok = true → (X.lo : ℝ) ≤ x * s ∧ x * s ≤ X.hi

theorem S_pos_int : (0 : ℤ) < S := by decide

theorem S_pos : (0 : ℝ) < S := by exact_mod_cast S_pos_int

theorem S_eq : S = 16777216 * S88 := by decide

theorem SM_eq : SM = S * TWO_M := by decide

theorem TWO_M_eq : (TWO_M : ℝ) = 2 ^ M := by norm_num [TWO_M, M]

/-! ## Rounding -/

theorem fdiv_mul_le (a b : ℤ) (hb : 0 < b) : ((fdiv a b : ℤ) : ℝ) * b ≤ a := by
  have := Int.ediv_mul_le a hb.ne'
  exact_mod_cast this

theorem le_cdiv_mul (a b : ℤ) (hb : 0 < b) : (a : ℝ) ≤ ((cdiv a b : ℤ) : ℝ) * b := by
  have h := Int.ediv_mul_le (-a) hb.ne'
  have h' : ((((-a) / b : ℤ)) : ℝ) * b ≤ -a := by exact_mod_cast h
  unfold cdiv
  push_cast
  linarith

theorem fdiv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ fdiv a b := Int.ediv_nonneg ha hb.le

/-! ## Basic operations -/

theorem memAt_zero (s : ℝ) : memAt s 0 zero := by
  intro _
  simp [zero]

theorem memAt_one : memAt S 1 one := by
  intro _
  simp [one]

theorem memAt_add {s x y : ℝ} {X Y : Iv} (hx : memAt s x X) (hy : memAt s y Y) :
    memAt s (x + y) (add X Y) := by
  intro h
  simp only [add, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := hx h.1
  obtain ⟨h3, h4⟩ := hy h.2
  simp only [add, Int.cast_add, add_mul]
  constructor <;> linarith

theorem memAt_neg {s x : ℝ} {X : Iv} (hx : memAt s x X) : memAt s (-x) (neg X) := by
  intro h
  obtain ⟨h1, h2⟩ := hx h
  simp only [neg, Int.cast_neg, neg_mul]
  constructor <;> linarith

theorem memAt_mulZ {s x : ℝ} {X : Iv} (w : ℤ) (hx : memAt s x X) : memAt s (w * x) (mulZ w X) := by
  unfold mulZ
  split_ifs with hw
  · intro h
    obtain ⟨h1, h2⟩ := hx h
    have hw' : (0 : ℝ) ≤ w := by exact_mod_cast hw
    simp only [Int.cast_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_left h1 hw', mul_le_mul_of_nonneg_left h2 hw'⟩
  · intro h
    obtain ⟨h1, h2⟩ := hx h
    have hw' : (w : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hw))
    simp only [Int.cast_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonpos_left h2 hw', mul_le_mul_of_nonpos_left h1 hw'⟩

/-- Four-corner bounds for a product of two reals in boxes. -/
theorem corner {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  constructor
  · rcases le_total 0 y with hy | hy
    · have h1 : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy
      rcases le_total 0 a with ha | ha
      · have h2 : a * c ≤ a * y := mul_le_mul_of_nonneg_left hy1 ha
        have h3 := le_trans (min_le_left (min (a * c) (a * d)) (min (b * c) (b * d))) (min_le_left _ _)
        linarith
      · have h2 : a * d ≤ a * y := mul_le_mul_of_nonpos_left hy2 ha
        have h3 := le_trans (min_le_left (min (a * c) (a * d)) (min (b * c) (b * d))) (min_le_right _ _)
        linarith
    · have h1 : b * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy
      rcases le_total 0 b with hb | hb
      · have h2 : b * c ≤ b * y := mul_le_mul_of_nonneg_left hy1 hb
        have h3 := le_trans (min_le_right (min (a * c) (a * d)) (min (b * c) (b * d))) (min_le_left _ _)
        linarith
      · have h2 : b * d ≤ b * y := mul_le_mul_of_nonpos_left hy2 hb
        have h3 := le_trans (min_le_right (min (a * c) (a * d)) (min (b * c) (b * d))) (min_le_right _ _)
        linarith
  · rcases le_total 0 y with hy | hy
    · have h1 : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx2 hy
      rcases le_total 0 b with hb | hb
      · have h2 : b * y ≤ b * d := mul_le_mul_of_nonneg_left hy2 hb
        have h3 := le_trans (le_max_right (b * c) (b * d)) (le_max_right (max (a * c) (a * d)) _)
        linarith
      · have h2 : b * y ≤ b * c := mul_le_mul_of_nonpos_left hy1 hb
        have h3 := le_trans (le_max_left (b * c) (b * d)) (le_max_right (max (a * c) (a * d)) _)
        linarith
    · have h1 : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx1 hy
      rcases le_total 0 a with ha | ha
      · have h2 : a * y ≤ a * d := mul_le_mul_of_nonneg_left hy2 ha
        have h3 := le_trans (le_max_right (a * c) (a * d)) (le_max_left _ (max (b * c) (b * d)))
        linarith
      · have h2 : a * y ≤ a * c := mul_le_mul_of_nonpos_left hy1 ha
        have h3 := le_trans (le_max_left (a * c) (a * d)) (le_max_left _ (max (b * c) (b * d)))
        linarith

theorem memAt_mulRaw {s t x y : ℝ} {X Y : Iv} (hx : memAt s x X) (hy : memAt t y Y) :
    memAt (s * t) (x * y) (mulRaw X Y) := by
  intro h
  simp only [mulRaw, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := hx h.1
  obtain ⟨h3, h4⟩ := hy h.2
  have hc := corner h1 h2 h3 h4
  have e : x * y * (s * t) = (x * s) * (y * t) := by ring
  simp only [mulRaw, Int.cast_min, Int.cast_max, Int.cast_mul, e]
  exact hc

theorem memAt_downBy {s x : ℝ} {X : Iv} {d : ℤ} (hd : 0 < d) (hx : memAt (s * d) x X) :
    memAt s x (downBy d X) := by
  intro h
  obtain ⟨h1, h2⟩ := hx h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have f1 := fdiv_mul_le X.lo d hd
  have f2 := le_cdiv_mul X.hi d hd
  simp only [downBy]
  constructor
  · apply le_of_mul_le_mul_right _ hd'
    calc ((fdiv X.lo d : ℤ) : ℝ) * d ≤ X.lo := f1
      _ ≤ x * (s * d) := h1
      _ = x * s * d := by ring
  · apply le_of_mul_le_mul_right _ hd'
    calc x * s * d = x * (s * d) := by ring
      _ ≤ X.hi := h2
      _ ≤ ((cdiv X.hi d : ℤ) : ℝ) * d := f2

theorem memAt_mul {x y : ℝ} {X Y : Iv} (hx : memAt S x X) (hy : memAt S y Y) :
    memAt S (x * y) (mul X Y) :=
  memAt_downBy S_pos_int (memAt_mulRaw hx hy)

theorem memAt_recip {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S x⁻¹ (recip X) := by
  intro h
  simp only [recip, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := hx h.1
  have hlo : (0 : ℝ) < X.lo := by exact_mod_cast h.2
  have hS := S_pos
  have hxS : 0 < x * S := lt_of_lt_of_le hlo h1
  have hx0 : 0 < x := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hhi : (0 : ℝ) < X.hi := lt_of_lt_of_le hxS h2
  have hhi' : 0 < X.hi := by exact_mod_cast hhi
  have hSS : (0 : ℤ) ≤ S * S := mul_nonneg S_pos_int.le S_pos_int.le
  simp only [recip]
  constructor
  · -- f * hi ≤ S^2 and x * S ≤ hi give f * x ≤ S, i.e. f ≤ x⁻¹ * S
    have f1 := fdiv_mul_le (S * S) X.hi hhi'
    have f0 : (0 : ℝ) ≤ ((fdiv (S * S) X.hi : ℤ) : ℝ) := by exact_mod_cast fdiv_nonneg hSS hhi'
    push_cast at f1
    have key : ((fdiv (S * S) X.hi : ℤ) : ℝ) * x ≤ S := by
      have := mul_le_mul_of_nonneg_left h2 f0
      nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hx0]
    exact key
  · have f2 := le_cdiv_mul (S * S) X.lo h.2
    push_cast at f2
    have c0 : (0 : ℝ) ≤ ((cdiv (S * S) X.lo : ℤ) : ℝ) := by
      by_contra hc
      push_neg at hc
      have : (0 : ℝ) < (S : ℝ) * S := mul_pos hS hS
      nlinarith
    have key : (S : ℝ) ≤ ((cdiv (S * S) X.lo : ℤ) : ℝ) * x := by
      have := mul_le_mul_of_nonneg_left h1 c0
      nlinarith
    rw [inv_mul_eq_div, div_le_iff₀ hx0]
    exact key

theorem memAt_relu {s x : ℝ} {X : Iv} (hs : 0 < s) (hx : memAt s x X) : memAt s (max 0 x) (relu X) := by
  intro h
  obtain ⟨h1, h2⟩ := hx h
  simp only [relu, Int.cast_max, Int.cast_zero]
  rw [max_mul_of_nonneg _ _ hs.le, zero_mul]
  exact ⟨max_le_max le_rfl h1, max_le_max le_rfl h2⟩

theorem memAt_ofW (z : ℤ) : memAt S ((z : ℝ) / 16777216) (ofW z) := by
  intro _
  have e : (S : ℝ) = 16777216 * S88 := by exact_mod_cast S_eq
  simp only [ofW, Int.cast_mul, e]
  constructor <;> apply le_of_eq <;> ring

/-! ## Exponential -/

theorem sqLo_spec : ∀ (k : ℕ) (a : ℤ) (z : ℝ), 0 ≤ a → (a : ℝ) ≤ Real.exp z * S →
    (sqLo k a : ℝ) ≤ Real.exp (2 ^ k * z) * S
  | 0, a, z, _, h => by simpa [sqLo] using h
  | k + 1, a, z, h0, h => by
    simp only [sqLo]
    have hS := S_pos
    have hf0 : 0 ≤ fdiv (a * a) S := fdiv_nonneg (mul_nonneg h0 h0) S_pos_int
    have hf : (fdiv (a * a) S : ℝ) ≤ Real.exp (2 * z) * S := by
      have f1 := fdiv_mul_le (a * a) S S_pos_int
      push_cast at f1
      have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast h0
      have h2 : (a : ℝ) * a ≤ (Real.exp z * S) * (Real.exp z * S) := mul_le_mul h h ha0 (le_trans ha0 h)
      have h3 : Real.exp (2 * z) = Real.exp z * Real.exp z := by rw [two_mul, Real.exp_add]
      rw [h3]
      apply le_of_mul_le_mul_right _ hS
      nlinarith
    have := sqLo_spec k (fdiv (a * a) S) (2 * z) hf0 hf
    rwa [show (2 : ℝ) ^ (k + 1) * z = 2 ^ k * (2 * z) by ring]

theorem sqHi_spec : ∀ (k : ℕ) (a : ℤ) (z : ℝ), Real.exp z * S ≤ a →
    Real.exp (2 ^ k * z) * S ≤ (sqHi k a : ℝ)
  | 0, a, z, h => by simpa [sqHi] using h
  | k + 1, a, z, h => by
    simp only [sqHi]
    have hS := S_pos
    have hf : Real.exp (2 * z) * S ≤ (cdiv (a * a) S : ℝ) := by
      have f2 := le_cdiv_mul (a * a) S S_pos_int
      push_cast at f2
      have he : 0 ≤ Real.exp z * S := by positivity
      have h2 : (Real.exp z * S) * (Real.exp z * S) ≤ (a : ℝ) * a := mul_le_mul h h he (le_trans he h)
      have h3 : Real.exp (2 * z) = Real.exp z * Real.exp z := by rw [two_mul, Real.exp_add]
      rw [h3]
      apply le_of_mul_le_mul_right _ hS
      nlinarith
    have := sqHi_spec k (cdiv (a * a) S) (2 * z) hf
    rwa [show (2 : ℝ) ^ (k + 1) * z = 2 ^ k * (2 * z) by ring]

theorem SM_real : (SM : ℝ) = S * 2 ^ M := by
  rw [← TWO_M_eq]
  exact_mod_cast SM_eq

theorem SM_pos : (0 : ℝ) < SM := by
  rw [SM_real]
  exact mul_pos S_pos (by positivity)

theorem expLo_spec (n : ℤ) : (expLo n : ℝ) ≤ Real.exp (n / S) * S := by
  unfold expLo
  have hS := S_pos
  set y : ℝ := n / SM with hy
  have base : ((max 0 (S + fdiv n TWO_M) : ℤ) : ℝ) ≤ Real.exp y * S := by
    have hT : (0 : ℝ) < TWO_M := by rw [TWO_M_eq]; positivity
    have hT' : (0 : ℤ) < TWO_M := by exact_mod_cast hT
    have f1 := fdiv_mul_le n TWO_M hT'
    have hfd : ((fdiv n TWO_M : ℤ) : ℝ) ≤ n / TWO_M := by rw [le_div_iff₀ hT]; exact f1
    have e1 : (n : ℝ) / TWO_M = y * S := by
      rw [hy, SM_real, ← TWO_M_eq]
      field_simp
    have hexp := Real.add_one_le_exp y
    push_cast
    apply max_le (by positivity)
    nlinarith
  have := sqLo_spec M _ y (le_max_left _ _) base
  have e2 : (2 : ℝ) ^ M * y = n / S := by
    rw [hy, SM_real]
    field_simp
  rwa [e2] at this

theorem expHi_spec (n : ℤ) (hn : n < SM) : Real.exp (n / S) * S ≤ (expHi n : ℝ) := by
  unfold expHi
  have hS := S_pos
  have hSM := SM_pos
  set y : ℝ := n / SM with hy
  have hD : (0 : ℤ) < SM - n := by omega
  have hD' : (0 : ℝ) < SM - n := by exact_mod_cast hD
  have base : Real.exp y * S ≤ ((cdiv (S * SM) (SM - n) : ℤ) : ℝ) := by
    have f2 := le_cdiv_mul (S * SM) (SM - n) hD
    push_cast at f2
    -- exp y ≤ 1 / (1 - y) = SM / (SM - n)
    have hy1 : 0 < 1 - y := by
      rw [hy, sub_pos, div_lt_one hSM]
      exact_mod_cast hn
    have hexp : Real.exp y * (1 - y) ≤ 1 := by
      have h1 := Real.add_one_le_exp (-y)
      have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      have h3 : 0 < Real.exp y := Real.exp_pos y
      nlinarith
    have e1 : (1 - y) * SM = SM - n := by
      rw [hy]
      field_simp
    have h4 : Real.exp y * S * (SM - n) ≤ S * SM := by
      rw [← e1]
      have := mul_le_mul_of_nonneg_right hexp (le_of_lt (mul_pos hS hSM))
      nlinarith
    apply le_of_mul_le_mul_right _ hD'
    linarith
  have := sqHi_spec M _ y base
  have e2 : (2 : ℝ) ^ M * y = n / S := by
    rw [hy, SM_real]
    field_simp
  rwa [e2] at this

theorem memAt_exp {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (Real.exp x) (expI X) := by
  intro h
  simp only [expI, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := hx h.1
  have hS := S_pos
  simp only [expI]
  constructor
  · have hle : (X.lo : ℝ) / S ≤ x := by rw [div_le_iff₀ hS]; exact h1
    calc (expLo X.lo : ℝ) ≤ Real.exp (X.lo / S) * S := expLo_spec X.lo
      _ ≤ Real.exp x * S := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) hS.le
  · have hle : x ≤ (X.hi : ℝ) / S := by rw [le_div_iff₀ hS]; exact h2
    calc Real.exp x * S ≤ Real.exp (X.hi / S) * S :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) hS.le
      _ ≤ (expHi X.hi : ℝ) := expHi_spec X.hi h.2




/-! ## Relational list lemmas (from the tiny development) -/

section ListRel

variable {α β γ δ ε ζ : Type*}

theorem f2_map_same {R : γ → δ → Prop} {f : α → γ} {g : α → δ} (H : ∀ a, R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.map f) (l.map g)
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (H a) (f2_map_same H l)

theorem f2_map {R : α → β → Prop} {R' : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (H : ∀ a b, R a b → R' (f a) (g b)) :
    ∀ {l : List α} {L : List β}, List.Forall₂ R l L → List.Forall₂ R' (l.map f) (L.map g)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (f2_map H t)

theorem f2_zipWith_left {R : β → δ → Prop} {R' : ε → ζ → Prop} {f : α → β → ε} {g : α → δ → ζ}
    (H : ∀ a b d, R b d → R' (f a b) (g a d)) :
    ∀ (l : List α) {x : List β} {X : List δ}, List.Forall₂ R x X →
      List.Forall₂ R' (List.zipWith f l x) (List.zipWith g l X)
  | [], _, _, _ => by simp
  | _ :: _, _, _, .nil => by simp
  | a :: l, _, _, .cons h t => by
    simp only [List.zipWith_cons_cons]
    exact .cons (H _ _ _ h) (f2_zipWith_left H l t)

theorem f2_zipWith {R₁ : α → β → Prop} {R₂ : γ → δ → Prop} {R : ε → ζ → Prop}
    {f : α → γ → ε} {g : β → δ → ζ} (H : ∀ a b c d, R₁ a b → R₂ c d → R (f a c) (g b d)) :
    ∀ {l₁ : List α} {L₁ : List β} {l₂ : List γ} {L₂ : List δ}, List.Forall₂ R₁ l₁ L₁ →
      List.Forall₂ R₂ l₂ L₂ → List.Forall₂ R (List.zipWith f l₁ l₂) (List.zipWith g L₁ L₂)
  | _, _, _, _, .nil, _ => by simp
  | _, _, _, _, .cons _ _, .nil => by simp
  | _, _, _, _, .cons h t, .cons h' t' => by
    simp only [List.zipWith_cons_cons]
    exact .cons (H _ _ _ _ h h') (f2_zipWith H t t')

theorem f2_getD {R : α → β → Prop} {d : α} {D : β} (hd : R d D) :
    ∀ {l : List α} {L : List β}, List.Forall₂ R l L → ∀ i, R (l.getD i d) (L.getD i D)
  | _, _, .nil, _ => by simpa using hd
  | _, _, .cons h _, 0 => by simpa using h
  | _, _, .cons _ t, i + 1 => by simpa using f2_getD hd t i

theorem f2_drop {R : α → β → Prop} :
    ∀ (n : ℕ) {l : List α} {L : List β}, List.Forall₂ R l L → List.Forall₂ R (l.drop n) (L.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => by simp
  | n + 1, _, _, .cons _ t => by simpa using f2_drop n t

theorem f2_take {R : α → β → Prop} :
    ∀ (n : ℕ) {l : List α} {L : List β}, List.Forall₂ R l L → List.Forall₂ R (l.take n) (L.take n)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, .nil => by simp
  | n + 1, _, _, .cons h t => by simpa using ⟨h, f2_take n t⟩

theorem f2_append {R : α → β → Prop} :
    ∀ {l₁ : List α} {L₁ : List β} {l₂ : List α} {L₂ : List β}, List.Forall₂ R l₁ L₁ →
      List.Forall₂ R l₂ L₂ → List.Forall₂ R (l₁ ++ l₂) (L₁ ++ L₂)
  | _, _, _, _, .nil, h => by simpa using h
  | _, _, _, _, .cons h t, h' => by simpa using ⟨h, f2_append t h'⟩

theorem f2_flatMap_same {R : γ → δ → Prop} {f : α → List γ} {g : α → List δ}
    (H : ∀ a, List.Forall₂ R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons]
    exact f2_append (H a) (f2_flatMap_same H l)

end ListRel

/-! ## Linear layers with float16 weights -/

/-- The real weight with integer numerator `z`: `z / 2^24`. -/
noncomputable def wt (z : ℤ) : ℝ := (z : ℝ) / 2 ^ 24

/-- Integer numerators (over `2^24`) of a packed row of `m` float16 entries. -/
def rowZ (m r : Nat) : List Int := (List.range m).map fun j => f16num (field r j)

theorem row_eq (m r : ℕ) : row m r = (rowZ m r).map wt := by
  simp only [row, rowZ, List.map_map]
  rfl

theorem memAt_sum {s : ℝ} :
    ∀ {l : List ℝ} {L : List Iv}, List.Forall₂ (memAt s) l L → memAt s l.sum (sumI L)
  | _, _, .nil => by simpa [sumI] using memAt_zero s
  | _, _, .cons h t => by
    simp only [List.sum_cons, sumI, List.foldr_cons]
    exact memAt_add h (memAt_sum t)

/-- Dividing the value by `d` is the same enclosure at scale `s * d`. -/
theorem memAt_scale {s x : ℝ} {X : Iv} {d : ℝ} (hd : d ≠ 0) (hx : memAt s x X) :
    memAt (s * d) (x / d) X := by
  intro h
  obtain ⟨h1, h2⟩ := hx h
  have e : x / d * (s * d) = x * s := by field_simp
  rw [e]
  exact ⟨h1, h2⟩

theorem memAt_wt (z : ℤ) : memAt S (wt z) (ofW z) := by
  have h := memAt_ofW z
  have e : wt z = (z : ℝ) / 16777216 := by unfold wt; norm_num
  rw [e]
  exact h

theorem memAt_wtMul {x : ℝ} {X : Iv} (w : ℤ) (hx : memAt S x X) :
    memAt (S * ((16777216 : ℤ) : ℝ)) (wt w * x) (mulZ w X) := by
  have h := memAt_mulZ w hx
  intro hok
  obtain ⟨h1, h2⟩ := h hok
  have e : wt w * x * (S * ((16777216 : ℤ) : ℝ)) = w * x * S := by
    unfold wt
    push_cast
    ring
  rw [e]
  exact ⟨h1, h2⟩

theorem memAt_dotWI (rowz : List ℤ) {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    memAt S (dot (rowz.map wt) x) (dotWI rowz X) := by
  unfold dot dotWI
  apply memAt_downBy (by norm_num)
  apply memAt_sum
  rw [List.zipWith_map_left]
  exact f2_zipWith_left (R := memAt S) (R' := memAt (S * ((16777216 : ℤ) : ℝ)))
    (f := fun a b => wt a * b) (g := mulZ) (fun w _ _ h => memAt_wtMul w h) rowz hx

theorem f2_vadd {x y : List ℝ} {X Y : List Iv} (hx : List.Forall₂ (memAt S) x X)
    (hy : List.Forall₂ (memAt S) y Y) : List.Forall₂ (memAt S) (vadd x y) (vaddI X Y) :=
  f2_zipWith (R₁ := memAt S) (R₂ := memAt S) (R := memAt S) (f := fun a b => a + b) (g := add)
    (fun _ _ _ _ h h' => memAt_add h h') hx hy

theorem f2_wt (l : List ℤ) : List.Forall₂ (memAt S) (l.map wt) (l.map ofW) :=
  f2_map_same (fun z => memAt_wt z) l

/-- Interval version of `vadd (mv (mat m rs) x) (row nb b)`. -/
def affI (m : Nat) (rs : List Nat) (nb b : Nat) (X : List Iv) : List Iv :=
  vaddI (rs.map fun r => dotWI (rowZ m r) X) ((rowZ nb b).map ofW)

theorem f2_aff (m : ℕ) (rs : List ℕ) (nb b : ℕ) {x : List ℝ} {X : List Iv}
    (hx : List.Forall₂ (memAt S) x X) :
    List.Forall₂ (memAt S) (vadd (mv (mat m rs) x) (row nb b)) (affI m rs nb b X) := by
  unfold affI mv mat
  rw [List.map_map, row_eq nb b]
  refine f2_vadd ?_ (f2_wt _)
  apply f2_map_same
  intro r
  simp only [Function.comp_apply, row_eq]
  exact memAt_dotWI _ hx


/-! ## Square root and LayerNorm -/

def isqrtIter : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | k + 1, v, r => isqrtIter k v ((r + v / r) / 2)

/-- Candidate for `⌊√v⌋` by Newton's iteration. Its result is checked by `sqrtCert`, not trusted. -/
def isqrtN (v : Nat) : Nat :=
  let r := isqrtIter 20 v (2 ^ (Nat.log2 v / 2 + 1))
  if r * r ≤ v then r else r - 1

/-- `[a, b]` as an enclosure of a square root, valid when `0 ≤ a`, `0 ≤ b`, `a^2 ≤ V.lo`, `V.hi ≤ b^2`. -/
def sqrtCert (V : Iv) (a b : Int) : Iv :=
  ⟨a, b, V.ok && decide (0 ≤ a) && decide (0 ≤ b) && decide (a * a ≤ V.lo) && decide (V.hi ≤ b * b)⟩

/-- Square root of an interval at scale `S * S`; the result is at scale `S`. -/
def sqrtI (V : Iv) : Iv := sqrtCert V (isqrtN V.lo.toNat) (isqrtN V.hi.toNat + 1)

theorem memAt_sqrtCert {v : ℝ} {V : Iv} (a b : ℤ) (hv : memAt ((S : ℝ) * S) v V) :
    memAt S (Real.sqrt v) (sqrtCert V a b) := by
  intro h
  simp only [sqrtCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hok, ha0⟩, hb0⟩, ha⟩, hb⟩ := h
  obtain ⟨h1, h2⟩ := hv hok
  have hS := S_pos
  have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  have hb0' : (0 : ℝ) ≤ b := by exact_mod_cast hb0
  have ha' : (a : ℝ) * a ≤ V.lo := by exact_mod_cast ha
  have hb' : (V.hi : ℝ) ≤ b * b := by exact_mod_cast hb
  have hv0 : 0 ≤ v := by
    have h3 : 0 ≤ v * ((S : ℝ) * S) := le_trans (le_trans (mul_self_nonneg (a : ℝ)) ha') h1
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hS hS]
  have ht : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0
  have hts : 0 ≤ Real.sqrt v * S := mul_nonneg (Real.sqrt_nonneg v) hS.le
  have hsq : (Real.sqrt v * S) * (Real.sqrt v * S) = v * ((S : ℝ) * S) := by
    calc (Real.sqrt v * S) * (Real.sqrt v * S) = (Real.sqrt v * Real.sqrt v) * ((S : ℝ) * S) := by ring
      _ = v * ((S : ℝ) * S) := by rw [ht]
  simp only [sqrtCert]
  constructor
  · by_contra hc
    push_neg at hc
    have hap : (0 : ℝ) < a := lt_of_le_of_lt hts hc
    have h4 : (Real.sqrt v * S) * (Real.sqrt v * S) < (a : ℝ) * a :=
      calc (Real.sqrt v * S) * (Real.sqrt v * S) ≤ (Real.sqrt v * S) * a := mul_le_mul_of_nonneg_left hc.le hts
        _ < a * a := mul_lt_mul_of_pos_right hc hap
    linarith
  · by_contra hc
    push_neg at hc
    have htp : (0 : ℝ) < Real.sqrt v * S := lt_of_le_of_lt hb0' hc
    have h4 : (b : ℝ) * b < (Real.sqrt v * S) * (Real.sqrt v * S) :=
      calc (b : ℝ) * b ≤ b * (Real.sqrt v * S) := mul_le_mul_of_nonneg_left hc.le hb0'
        _ < (Real.sqrt v * S) * (Real.sqrt v * S) := mul_lt_mul_of_pos_right hc htp
    linarith

theorem memAt_sqrt {v : ℝ} {V : Iv} (hv : memAt ((S : ℝ) * S) v V) : memAt S (Real.sqrt v) (sqrtI V) :=
  memAt_sqrtCert _ _ hv

/-- `eps = 1e-5` at scale `S * S`. -/
def epsI : Iv := ⟨fdiv (S * S) 100000, cdiv (S * S) 100000, true⟩

theorem memAt_eps : memAt ((S : ℝ) * S) (1 / 100000) epsI := by
  intro _
  have f1 := fdiv_mul_le (S * S) 100000 (by norm_num)
  have f2 := le_cdiv_mul (S * S) 100000 (by norm_num)
  push_cast at f1 f2
  simp only [epsI]
  constructor <;> linarith

/-- Interval LayerNorm; `g`, `b` are the integer numerators (over `2^24`) of gain and bias. -/
def layerNormI (g b : List Int) (X : List Iv) : List Iv :=
  vaddI (List.zipWith (fun gi c => downBy 16777216 (mulZ gi (mul c
    (recip (sqrtI (add (downBy (X.length : Int) (sumI ((X.map fun x => add x (neg (downBy (X.length : Int) (sumI X)))).map
      fun c => mulRaw c c))) epsI))))))
    g (X.map fun x => add x (neg (downBy (X.length : Int) (sumI X))))) (b.map ofW)

theorem f2_layerNorm (g b : List ℤ) {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    List.Forall₂ (memAt S) (layerNorm (g.map wt) (b.map wt) x) (layerNormI g b X) := by
  rcases Nat.eq_zero_or_pos x.length with h0 | hpos
  · have hx0 : x = [] := List.eq_nil_of_length_eq_zero h0
    subst hx0
    cases hx
    simp [layerNorm, layerNormI, vadd, vaddI]
  · have hlen : X.length = x.length := hx.length_eq.symm
    have hd : (0 : ℤ) < (X.length : ℤ) := by rw [hlen]; exact_mod_cast hpos
    have hdR : (x.length : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have ed : (((X.length : ℤ)) : ℝ) = (x.length : ℝ) := by rw [hlen]; norm_cast
    have hmu : memAt S (x.sum / (x.length : ℝ)) (downBy (X.length : ℤ) (sumI X)) := by
      apply memAt_downBy hd
      rw [ed]
      exact memAt_scale hdR (memAt_sum hx)
    have hC : List.Forall₂ (memAt S) (x.map fun a => a - x.sum / (x.length : ℝ))
        (X.map fun x => add x (neg (downBy (X.length : ℤ) (sumI X)))) :=
      f2_map (fun a A h => by rw [sub_eq_add_neg]; exact memAt_add h (memAt_neg hmu)) hx
    have hsq : List.Forall₂ (memAt ((S : ℝ) * S)) (x.map fun a => (a - x.sum / (x.length : ℝ)) ^ 2)
        ((X.map fun x => add x (neg (downBy (X.length : ℤ) (sumI X)))).map fun c => mulRaw c c) := by
      have h := f2_map (R' := memAt ((S : ℝ) * S)) (f := fun c : ℝ => c ^ 2) (g := fun c => mulRaw c c)
        (fun c C h => by simp only [sq]; exact memAt_mulRaw h h) hC
      rwa [List.map_map] at h
    have hvar : memAt ((S : ℝ) * S) ((x.map fun a => (a - x.sum / (x.length : ℝ)) ^ 2).sum / (x.length : ℝ))
        (downBy (X.length : ℤ) (sumI ((X.map fun x => add x (neg (downBy (X.length : ℤ) (sumI X)))).map
          fun c => mulRaw c c))) := by
      apply memAt_downBy hd
      rw [ed]
      exact memAt_scale hdR (memAt_sum hsq)
    have hinv := memAt_recip (memAt_sqrt (memAt_add hvar memAt_eps))
    simp only [layerNorm, layerNormI]
    refine f2_vadd ?_ (f2_wt b)
    rw [List.zipWith_map_left, List.zipWith_map_right]
    refine f2_zipWith_left (R := memAt S) (R' := memAt S) ?_ g hx
    intro gi a A h
    apply memAt_downBy (by norm_num)
    refine memAt_wtMul gi ?_
    rw [div_eq_mul_inv, sub_eq_add_neg]
    exact memAt_mul (memAt_add h (memAt_neg hmu)) hinv



/-! ## The Gaussian integral, `Phi` and GELU -/

/-- Division of the value by a positive integer, rounded outward. -/
theorem memAt_divZ {x : ℝ} {X : Iv} (d : ℤ) (hd : 0 < d) (hx : memAt S x X) :
    memAt S (x / (d : ℝ)) (downBy d X) :=
  memAt_downBy hd (memAt_scale (by exact_mod_cast hd.ne') hx)

/-- Series loop: `k` more terms from index `n`, with current term `T` and partial sum `G`. -/
def gLoop (X2 : Iv) : Nat → Nat → Iv → Iv → Iv × Iv
  | 0, _, T, G => (G, T)
  | k + 1, n, T, G => gLoop X2 k (n + 1) (downBy (2 * (n : Int) + 3) (mul T X2)) (add G T)

theorem gLoop_sound {x : ℝ} {X2 : Iv} (h2 : memAt S (x ^ 2) X2) :
    ∀ (k n : ℕ) (T G : Iv), memAt S (dco (n + 1) * x ^ (2 * n + 1)) T → memAt S (gser n x) G →
      memAt S (gser (n + k) x) (gLoop X2 k n T G).1 ∧
        memAt S (dco (n + k + 1) * x ^ (2 * (n + k) + 1)) (gLoop X2 k n T G).2
  | 0, n, T, G, hT, hG => by simpa [gLoop] using ⟨hG, hT⟩
  | k + 1, n, T, G, hT, hG => by
    have hT' : memAt S (dco (n + 1 + 1) * x ^ (2 * (n + 1) + 1))
        (downBy (2 * (n : ℤ) + 3) (mul T X2)) := by
      have h := memAt_divZ (2 * (n : ℤ) + 3) (by positivity) (memAt_mul hT h2)
      have e : dco (n + 1 + 1) * x ^ (2 * (n + 1) + 1) =
          dco (n + 1) * x ^ (2 * n + 1) * x ^ 2 / ((2 * (n : ℤ) + 3 : ℤ) : ℝ) := by
        have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
        have e2 : dco (n + 1 + 1) = dco (n + 1) / (2 * (n : ℝ) + 3) := by
          show dco (n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1) = dco (n + 1) / (2 * (n : ℝ) + 3)
          push_cast
          ring_nf
        rw [e2]
        push_cast
        field_simp
        ring
      rw [e]
      exact h
    have hG' : memAt S (gser (n + 1) x) (add G T) := memAt_add hG hT
    have h := gLoop_sound h2 k (n + 1) _ _ hT' hG'
    have e1 : n + 1 + k = n + (k + 1) := by omega
    rw [e1] at h
    exact h

/-- `[min 0 lo, max 0 hi]`. -/
def hull0 (R : Iv) : Iv := ⟨min 0 R.lo, max 0 R.hi, R.ok⟩

theorem memAt_hull0 {r u : ℝ} {R : Iv} (hr : memAt S r R) (h1 : min 0 r ≤ u) (h2 : u ≤ max 0 r) :
    memAt S u (hull0 R) := by
  intro h
  obtain ⟨a, b⟩ := hr h
  have hS := S_pos
  simp only [hull0, Int.cast_min, Int.cast_max, Int.cast_zero]
  constructor
  · rcases le_total 0 r with hr0 | hr0
    · have h3 : 0 ≤ u := by rwa [min_eq_left hr0] at h1
      exact le_trans (min_le_left _ _) (mul_nonneg h3 hS.le)
    · have h3 : r ≤ u := by rwa [min_eq_right hr0] at h1
      exact le_trans (min_le_right _ _) (le_trans a (mul_le_mul_of_nonneg_right h3 hS.le))
  · rcases le_total 0 r with hr0 | hr0
    · have h3 : u ≤ r := by rwa [max_eq_right hr0] at h2
      exact le_trans (le_trans (mul_le_mul_of_nonneg_right h3 hS.le) b) (le_max_right _ _)
    · have h3 : u ≤ 0 := by rwa [max_eq_left hr0] at h2
      have h4 : u * (S : ℝ) ≤ 0 := by nlinarith
      exact le_trans h4 (le_max_left _ _)

/-- Enclosure of `gaussInt x` by the series with `N` terms (`ok` requires `1 ≤ N` and `x^2 ≤ N + 1`). -/
def gaussSeriesI (X : Iv) (N : Nat) : Iv :=
  ⟨(mul (expI (downBy 2 (neg (mul X X))))
      (add (gLoop (mul X X) N 0 X zero).1
        (hull0 (downBy (N : Int) (mulZ (2 * (N : Int) + 1) (gLoop (mul X X) N 0 X zero).2))))).lo,
   (mul (expI (downBy 2 (neg (mul X X))))
      (add (gLoop (mul X X) N 0 X zero).1
        (hull0 (downBy (N : Int) (mulZ (2 * (N : Int) + 1) (gLoop (mul X X) N 0 X zero).2))))).hi,
   (mul (expI (downBy 2 (neg (mul X X))))
      (add (gLoop (mul X X) N 0 X zero).1
        (hull0 (downBy (N : Int) (mulZ (2 * (N : Int) + 1) (gLoop (mul X X) N 0 X zero).2))))).ok &&
     decide (1 ≤ N) && decide ((mul X X).ok = true) && decide ((mul X X).hi ≤ ((N : Int) + 1) * S)⟩

theorem memAt_gaussSeries {x : ℝ} {X : Iv} (N : ℕ) (hx : memAt S x X) :
    memAt S (gaussInt x) (gaussSeriesI X N) := by
  intro h
  simp only [gaussSeriesI, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hN⟩, hok2⟩, hbd⟩ := h
  have hS := S_pos
  have h2 : memAt S (x ^ 2) (mul X X) := by rw [sq]; exact memAt_mul hx hx
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx2 : x ^ 2 ≤ (N : ℝ) + 1 := by
    have h3 := (h2 hok2).2
    have h4 : (((mul X X).hi : ℤ) : ℝ) ≤ ((N : ℝ) + 1) * S := by exact_mod_cast hbd
    have h5 : x ^ 2 * S ≤ ((N : ℝ) + 1) * S := le_trans h3 h4
    exact le_of_mul_le_mul_right h5 hS
  have hE : memAt S (Real.exp (-(x ^ 2) / 2)) (expI (downBy 2 (neg (mul X X)))) := by
    have h3 := memAt_divZ 2 (by norm_num) (memAt_neg h2)
    have e : -(x ^ 2) / ((2 : ℤ) : ℝ) = -(x ^ 2) / 2 := by norm_num
    rw [e] at h3
    exact memAt_exp h3
  have hT0 : memAt S (dco (0 + 1) * x ^ (2 * 0 + 1)) X := by
    have e : dco (0 + 1) * x ^ (2 * 0 + 1) = x := by simp [dco]
    rw [e]
    exact hx
  have hG0 : memAt S (gser 0 x) zero := by
    have e : gser 0 x = 0 := rfl
    rw [e]
    exact memAt_zero _
  obtain ⟨hG, hT⟩ := gLoop_sound h2 N 0 X zero hT0 hG0
  rw [Nat.zero_add] at hG hT
  have hR : memAt S (dco N / (N : ℝ) * x ^ (2 * N + 1))
      (downBy (N : ℤ) (mulZ (2 * (N : ℤ) + 1) (gLoop (mul X X) N 0 X zero).2)) := by
    have h3 := memAt_divZ (N : ℤ) (by exact_mod_cast hN) (memAt_mulZ (2 * (N : ℤ) + 1) hT)
    have e : dco N / (N : ℝ) * x ^ (2 * N + 1) =
        ((2 * (N : ℤ) + 1 : ℤ) : ℝ) * (dco (N + 1) * x ^ (2 * N + 1)) / ((N : ℤ) : ℝ) := by
      have h4 : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      have e2 : dco (N + 1) = dco N / (2 * (N : ℝ) + 1) := rfl
      rw [e2]
      push_cast
      field_simp
    rw [e]
    exact h3
  have he := Real.exp_pos (-(x ^ 2) / 2)
  obtain ⟨b1, b2⟩ := gaussInt_encl N hN x hx2
  have hw : memAt S (gaussInt x / Real.exp (-(x ^ 2) / 2))
      (add (gLoop (mul X X) N 0 X zero).1
        (hull0 (downBy (N : ℤ) (mulZ (2 * (N : ℤ) + 1) (gLoop (mul X X) N 0 X zero).2)))) := by
    have e : gaussInt x / Real.exp (-(x ^ 2) / 2) =
        gser N x + (gaussInt x / Real.exp (-(x ^ 2) / 2) - gser N x) := by ring
    rw [e]
    refine memAt_add hG (memAt_hull0 hR ?_ ?_)
    · rw [le_sub_iff_add_le, le_div_iff₀ he]
      linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ he]
      linarith
  have hF := memAt_mul hE hw
  have e : Real.exp (-(x ^ 2) / 2) * (gaussInt x / Real.exp (-(x ^ 2) / 2)) = gaussInt x := by
    field_simp
  rw [e] at hF
  exact hF hok



/-! ## Tails, `Phi` and GELU -/

/-- The point 12, where the tail rule takes over. -/
def A12 : Iv := ⟨12 * S, 12 * S, true⟩

/-- Enclosure of `gaussInt 12`. -/
def FA : Iv := gaussSeriesI A12 348

/-- Enclosure of `exp (-72)`. -/
def EA : Iv := expI ⟨-(72 * S), -(72 * S), true⟩

theorem memAt_A12 : memAt S 12 A12 := by
  intro _
  simp only [A12]
  push_cast
  exact ⟨le_rfl, le_rfl⟩

theorem memAt_FA : memAt S (gaussInt 12) FA := memAt_gaussSeries 348 memAt_A12

theorem memAt_EA : memAt S (Real.exp (-72)) EA := by
  apply memAt_exp
  intro _
  push_cast
  constructor <;> linarith

theorem tail_bound {y : ℝ} {B : ℤ} (hF : FA.ok = true) (hE : EA.ok = true) (h12 : (12 : ℝ) ≤ y)
    (hB : y * S ≤ (B : ℝ)) :
    (FA.lo : ℝ) ≤ gaussInt y * S ∧
      gaussInt y * S ≤ ((FA.hi + cdiv ((B - 12 * S) * EA.hi) S : ℤ) : ℝ) := by
  obtain ⟨f1, f2⟩ := memAt_FA hF
  obtain ⟨e1, e2⟩ := memAt_EA hE
  have hS := S_pos
  have hm := gaussInt_mono h12
  have ht := gaussInt_tail 12 y (by norm_num) h12
  have e72 : Real.exp (-((12 : ℝ) ^ 2) / 2) = Real.exp (-72) := by norm_num
  rw [e72] at ht
  constructor
  · exact le_trans f1 (mul_le_mul_of_nonneg_right hm hS.le)
  · have c := le_cdiv_mul ((B - 12 * S) * EA.hi) S S_pos_int
    push_cast at c ⊢
    have d1 : (y - 12) * S ≤ (B : ℝ) - 12 * S := by linarith
    have d0 : 0 ≤ (y - 12) * (S : ℝ) := mul_nonneg (by linarith) hS.le
    have ex0 : 0 ≤ Real.exp (-72) * (S : ℝ) := mul_nonneg (Real.exp_pos _).le hS.le
    have p : (y - 12) * S * (Real.exp (-72) * S) ≤ ((B : ℝ) - 12 * S) * EA.hi :=
      mul_le_mul d1 e2 ex0 (le_trans d0 d1)
    have q : (y - 12) * Real.exp (-72) * S ≤ (cdiv ((B - 12 * S) * EA.hi) S : ℝ) := by
      apply le_of_mul_le_mul_right _ hS
      calc (y - 12) * Real.exp (-72) * S * S = (y - 12) * S * (Real.exp (-72) * S) := by ring
        _ ≤ ((B : ℝ) - 12 * S) * EA.hi := p
        _ ≤ (cdiv ((B - 12 * S) * EA.hi) S : ℝ) * S := c
    have r : gaussInt y * S ≤ (gaussInt 12 + (y - 12) * Real.exp (-72)) * S :=
      mul_le_mul_of_nonneg_right ht hS.le
    linarith

/-- Number of series terms used for the interval `X`. -/
def serN (X : Iv) : Nat := 2 * ((max X.lo.natAbs X.hi.natAbs) ^ 2 / (S.natAbs ^ 2) + 1) + 30

/-- Enclosure of `gaussInt x`: series for `|x| ≤ 12`, tail rule beyond. -/
def gaussI (X : Iv) : Iv :=
  if X.hi ≤ 12 * S ∧ -(12 * S) ≤ X.lo then gaussSeriesI X (serN X)
  else if 12 * S < X.lo then
    ⟨FA.lo, FA.hi + cdiv ((X.hi - 12 * S) * EA.hi) S, X.ok && FA.ok && EA.ok⟩
  else if X.hi < -(12 * S) then
    ⟨-(FA.hi + cdiv ((-X.lo - 12 * S) * EA.hi) S), -FA.lo, X.ok && FA.ok && EA.ok⟩
  else ⟨0, 0, false⟩

theorem memAt_gaussI {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (gaussInt x) (gaussI X) := by
  unfold gaussI
  have hS := S_pos
  split_ifs with h1 h2 h3
  · exact memAt_gaussSeries _ hx
  · intro hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hX, hF⟩, hE⟩ := hok
    obtain ⟨x1, x2⟩ := hx hX
    have h12 : (12 : ℝ) ≤ x := by
      have h4 : ((12 * S : ℤ) : ℝ) < X.lo := by exact_mod_cast h2
      push_cast at h4
      have h5 : 12 * (S : ℝ) < x * S := lt_of_lt_of_le h4 x1
      exact (lt_of_mul_lt_mul_right h5 hS.le).le
    exact tail_bound hF hE h12 x2
  · intro hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hX, hF⟩, hE⟩ := hok
    obtain ⟨x1, x2⟩ := hx hX
    have h12 : (12 : ℝ) ≤ -x := by
      have h4 : (X.hi : ℝ) < ((-(12 * S) : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      have h5 : x * S < -(12 * (S : ℝ)) := lt_of_le_of_lt x2 h4
      have h6 : x * S < (-12) * (S : ℝ) := by linarith
      have h7 := lt_of_mul_lt_mul_right h6 hS.le
      linarith
    have hB : -x * S ≤ ((-X.lo : ℤ) : ℝ) := by push_cast; linarith
    obtain ⟨t1, t2⟩ := tail_bound hF hE h12 hB
    rw [gaussInt_neg] at t1 t2
    push_cast at t1 t2 ⊢
    constructor <;> linarith
  · intro hok
    simp at hok

/-- `S / 2`. -/
def HALF : Int := 765859623936625360317110380697196002292931682211504247013376

theorem S_half : S = 2 * HALF := by decide

def halfI : Iv := ⟨HALF, HALF, true⟩

theorem memAt_half : memAt S (1 / 2) halfI := by
  intro _
  have e : (S : ℝ) = 2 * HALF := by exact_mod_cast S_half
  simp only [halfI, e]
  constructor <;> linarith

/-- `2 π` at scale `S * S`, from Mathlib's 20-digit bounds on `π`. -/
def twoPiI : Iv :=
  ⟨fdiv (628318530717958647692 * (S * S)) 100000000000000000000,
   cdiv (628318530717958647694 * (S * S)) 100000000000000000000, true⟩

theorem memAt_twoPi : memAt ((S : ℝ) * S) (2 * Real.pi) twoPiI := by
  intro _
  have f1 := fdiv_mul_le (628318530717958647692 * (S * S)) 100000000000000000000 (by norm_num)
  have f2 := le_cdiv_mul (628318530717958647694 * (S * S)) 100000000000000000000 (by norm_num)
  push_cast at f1 f2
  have hSS : (0 : ℝ) < (S : ℝ) * S := mul_pos S_pos S_pos
  have hA : (314159265358979323846 : ℝ) < Real.pi * 100000000000000000000 := by
    linarith [Real.pi_gt_d20]
  have hB : Real.pi * 100000000000000000000 < (314159265358979323847 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hA' := mul_lt_mul_of_pos_right hA hSS
  have hB' := mul_lt_mul_of_pos_right hB hSS
  simp only [twoPiI]
  constructor <;> linarith

/-- Enclosure of `1 / √(2π)`. -/
def c2piI : Iv := recip (sqrtI twoPiI)

theorem memAt_c2pi : memAt S (Real.sqrt (2 * Real.pi))⁻¹ c2piI :=
  memAt_recip (memAt_sqrt memAt_twoPi)

/-- Interval GELU. -/
def geluI (X : Iv) : Iv := mul X (add halfI (mul (gaussI X) c2piI))

theorem memAt_gelu {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (gelu x) (geluI X) := by
  have e : gelu x = x * (1 / 2 + gaussInt x * (Real.sqrt (2 * Real.pi))⁻¹) := by
    unfold gelu Phi gaussInt
    ring
  rw [e]
  exact memAt_mul hx (memAt_add memAt_half (memAt_mul (memAt_gaussI hx) memAt_c2pi))


/-! ## One-token forward pass in intervals

On a one-token prompt there is no softmax and no rotary: `lastHidden θ [t]` is the final LayerNorm of
`stepC` folded over the layers, started at the embedding row (`lastHidden_single`). `stepCI` mirrors
`stepC` operation by operation, for a layer given by its packed float16 rows. -/

/-- A layer as packed float16 rows (the format of `CON.W.L*`). -/
structure LayerZ where
  ln1g : Nat
  ln1b : Nat
  ln2g : Nat
  ln2b : Nat
  qkvW : List Nat
  qkvB : Nat
  oW : List Nat
  oB : Nat
  fW : List Nat
  fB : Nat
  pW : List Nat
  pB : Nat

/-- The real layer of a packed layer (the shape used in `CON.Pythia`). -/
noncomputable def LayerZ.toLayer (z : LayerZ) : Layer where
  ln1g := row 128 z.ln1g
  ln1b := row 128 z.ln1b
  ln2g := row 128 z.ln2g
  ln2b := row 128 z.ln2b
  qkvW := mat 128 z.qkvW
  qkvB := row 384 z.qkvB
  oW := mat 128 z.oW
  oB := row 128 z.oB
  fW := mat 128 z.fW
  fB := row 512 z.fB
  pW := mat 512 z.pW
  pB := row 128 z.pB

def qkvI (z : LayerZ) (U : List Iv) : List Iv := affI 128 z.qkvW 384 z.qkvB U

def attnCI (z : LayerZ) (U : List Iv) : List Iv :=
  affI 128 z.oW 128 z.oB ((List.range 4).flatMap fun h =>
    (List.range 32).map fun d => (((qkvI z U).drop (96 * h + 64)).take 32).getD d zero)

def mlpOutI (z : LayerZ) (U : List Iv) : List Iv :=
  affI 512 z.pW 128 z.pB ((affI 128 z.fW 512 z.fB U).map geluI)

def stepCI (z : LayerZ) (X : List Iv) : List Iv :=
  vaddI (vaddI X (attnCI z (layerNormI (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) X)))
    (mlpOutI z (layerNormI (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) X))

theorem f2_attnC (z : LayerZ) {u : List ℝ} {U : List Iv} (hu : List.Forall₂ (memAt S) u U) :
    List.Forall₂ (memAt S) (attnC z.toLayer u) (attnCI z U) := by
  have hq : List.Forall₂ (memAt S) (qkv z.toLayer u) (qkvI z U) := f2_aff 128 z.qkvW 384 z.qkvB hu
  unfold attnC attnCI
  exact f2_aff 128 z.oW 128 z.oB (f2_flatMap_same (fun h => f2_map_same (fun d =>
    f2_getD (memAt_zero S) (f2_take 32 (f2_drop (96 * h + 64) hq)) d) (List.range 32)) (List.range 4))

theorem f2_mlpOut (z : LayerZ) {u : List ℝ} {U : List Iv} (hu : List.Forall₂ (memAt S) u U) :
    List.Forall₂ (memAt S) (mlpOut z.toLayer u) (mlpOutI z U) := by
  simp only [mlpOut, mlpOutI, LayerZ.toLayer]
  have h1 : List.Forall₂ (memAt S) (vadd (mv (mat 128 z.fW) u) (row 512 z.fB)) (affI 128 z.fW 512 z.fB U) :=
    f2_aff 128 z.fW 512 z.fB hu
  have h2 : List.Forall₂ (memAt S) ((vadd (mv (mat 128 z.fW) u) (row 512 z.fB)).map gelu)
      ((affI 128 z.fW 512 z.fB U).map geluI) :=
    f2_map (R := memAt S) (R' := memAt S) (f := gelu) (g := geluI) (fun _ _ h => memAt_gelu h) h1
  exact f2_aff 512 z.pW 128 z.pB h2

theorem f2_stepC (z : LayerZ) {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    List.Forall₂ (memAt S) (stepC z.toLayer x) (stepCI z X) := by
  have h1 : List.Forall₂ (memAt S) (layerNorm z.toLayer.ln1g z.toLayer.ln1b x)
      (layerNormI (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) X) := by
    have h := f2_layerNorm (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) hx
    rw [← row_eq, ← row_eq] at h
    exact h
  have h2 : List.Forall₂ (memAt S) (layerNorm z.toLayer.ln2g z.toLayer.ln2b x)
      (layerNormI (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) X) := by
    have h := f2_layerNorm (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) hx
    rw [← row_eq, ← row_eq] at h
    exact h
  unfold stepC stepCI
  exact f2_vadd (f2_vadd hx (f2_attnC z h1)) (f2_mlpOut z h2)

/-! ## Boxes and checks -/

/-- `X` is valid and lies inside `B`. -/
def subI (X B : Iv) : Bool := X.ok && decide (B.lo ≤ X.lo) && decide (X.hi ≤ B.hi)

def allSub : List Iv → List Iv → Bool
  | [], [] => true
  | X :: Xs, B :: Bs => subI X B && allSub Xs Bs
  | _, _ => false

theorem memAt_sub {x : ℝ} {X B : Iv} (hx : memAt S x X) (h : subI X B = true) : memAt S x B := by
  intro _
  simp only [subI, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, h1⟩, h2⟩ := h
  obtain ⟨a, b⟩ := hx hok
  have h1' : (B.lo : ℝ) ≤ X.lo := by exact_mod_cast h1
  have h2' : (X.hi : ℝ) ≤ B.hi := by exact_mod_cast h2
  exact ⟨le_trans h1' a, le_trans b h2'⟩

theorem f2_sub : ∀ {x : List ℝ} {Xs Bs : List Iv}, List.Forall₂ (memAt S) x Xs → allSub Xs Bs = true →
    List.Forall₂ (memAt S) x Bs
  | _, _, [], .nil, _ => .nil
  | _, _, _ :: _, .nil, h => by simp [allSub] at h
  | _, _, [], .cons _ _, h => by simp [allSub] at h
  | _, _, _ :: _, .cons hx t, h => by
    simp only [allSub, Bool.and_eq_true] at h
    exact .cons (memAt_sub hx h.1) (f2_sub t h.2)

/-- The layer maps the box `Bin` into the box `Bout`. -/
def layerCheck (z : LayerZ) (Bin Bout : List Iv) : Bool := allSub (stepCI z Bin) Bout

theorem layer_ok (z : LayerZ) {x : List ℝ} {Bin Bout : List Iv} (hx : List.Forall₂ (memAt S) x Bin)
    (h : layerCheck z Bin Bout = true) : List.Forall₂ (memAt S) (stepC z.toLayer x) Bout :=
  f2_sub (f2_stepC z hx) h

/-- The embedding row as exact intervals. -/
def embI (e : Nat) : List Iv := (rowZ 128 e).map ofW

theorem f2_emb (e : ℕ) : List.Forall₂ (memAt S) (row 128 e) (embI e) := by
  rw [row_eq]
  exact f2_wt _

theorem lastHidden_single (θ : Params) (t : ℕ) :
    lastHidden θ [t] = layerNorm θ.lnfg θ.lnfb (θ.layers.foldl (fun y L => stepC L y) (θ.emb t)) := by
  have e : ([t] : List ℕ) = List.replicate 1 t := rfl
  rw [e]
  unfold lastHidden hidden
  rw [List.map_replicate, foldl_layer_const, List.length_replicate, List.getD_replicate _ (by omega)]

/-- Enclosure of `logit t1 - logit t0` from a box for the residual stream after the last layer;
`g`, `b` are the packed final LayerNorm, `u0`, `u1` the packed unembedding rows. -/
def logitDiffI (g b u0 u1 : Nat) (B : List Iv) : Iv :=
  add (dotWI (rowZ 128 u1) (layerNormI (rowZ 128 g) (rowZ 128 b) B))
    (neg (dotWI (rowZ 128 u0) (layerNormI (rowZ 128 g) (rowZ 128 b) B)))

theorem memAt_logitDiff (g b u0 u1 : ℕ) {x : List ℝ} {B : List Iv} (hx : List.Forall₂ (memAt S) x B) :
    memAt S (dot (row 128 u1) (layerNorm (row 128 g) (row 128 b) x) -
      dot (row 128 u0) (layerNorm (row 128 g) (row 128 b) x)) (logitDiffI g b u0 u1 B) := by
  have h := f2_layerNorm (rowZ 128 g) (rowZ 128 b) hx
  rw [← row_eq, ← row_eq] at h
  have h1 := memAt_dotWI (rowZ 128 u1) h
  have h0 := memAt_dotWI (rowZ 128 u0) h
  rw [← row_eq] at h1 h0
  rw [sub_eq_add_neg]
  exact memAt_add h1 (memAt_neg h0)

/-- The two-way probability from the logit difference: `1 / (1 + exp (-d))`. -/
def probI (D : Iv) : Iv := recip (add one (expI (neg D)))

theorem two_way (l0 l1 : ℝ) :
    Real.exp l1 / (Real.exp l0 + Real.exp l1) = (1 + Real.exp (-(l1 - l0)))⁻¹ := by
  have h0 := Real.exp_pos l0
  have h1 := Real.exp_pos l1
  have e : Real.exp (-(l1 - l0)) = Real.exp l0 / Real.exp l1 := by
    rw [neg_sub, Real.exp_sub]
  rw [e]
  field_simp
  ring

theorem memAt_prob {l0 l1 : ℝ} {D : Iv} (h : memAt S (l1 - l0) D) :
    memAt S (Real.exp l1 / (Real.exp l0 + Real.exp l1)) (probI D) := by
  rw [two_way]
  exact memAt_recip (memAt_add memAt_one (memAt_exp (memAt_neg h)))


/-! ## A layer step in three kernel checks

Splitting keeps each kernel computation small: the attention output, the GELU outputs, and the residual sum
with the MLP output map are checked against boxes separately. -/

/-- The attention output of the layer on the box `Bin` lies in `Batt`. -/
def attCheck (z : LayerZ) (Bin Batt : List Iv) : Bool :=
  allSub (attnCI z (layerNormI (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) Bin)) Batt

/-- The GELU outputs of the layer on the box `Bin` lie in `Bhid`. -/
def hidCheck (z : LayerZ) (Bin Bhid : List Iv) : Bool :=
  allSub ((affI 128 z.fW 512 z.fB (layerNormI (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) Bin)).map geluI) Bhid

/-- Input plus attention output plus MLP output (from the hidden box) lies in `Bout`. -/
def outCheck (z : LayerZ) (Bin Batt Bhid Bout : List Iv) : Bool :=
  allSub (vaddI (vaddI Bin Batt) (affI 512 z.pW 128 z.pB Bhid)) Bout

theorem layer_ok3 (z : LayerZ) {x : List ℝ} {Bin Batt Bhid Bout : List Iv}
    (hx : List.Forall₂ (memAt S) x Bin) (ha : attCheck z Bin Batt = true)
    (hh : hidCheck z Bin Bhid = true) (ho : outCheck z Bin Batt Bhid Bout = true) :
    List.Forall₂ (memAt S) (stepC z.toLayer x) Bout := by
  have h1 : List.Forall₂ (memAt S) (layerNorm z.toLayer.ln1g z.toLayer.ln1b x)
      (layerNormI (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) Bin) := by
    have h := f2_layerNorm (rowZ 128 z.ln1g) (rowZ 128 z.ln1b) hx
    rw [← row_eq, ← row_eq] at h
    exact h
  have h2 : List.Forall₂ (memAt S) (layerNorm (row 128 z.ln2g) (row 128 z.ln2b) x)
      (layerNormI (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) Bin) := by
    have h := f2_layerNorm (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) hx
    rw [← row_eq, ← row_eq] at h
    exact h
  have a : List.Forall₂ (memAt S) (attnC z.toLayer (layerNorm z.toLayer.ln1g z.toLayer.ln1b x)) Batt :=
    f2_sub (f2_attnC z h1) ha
  have hidr : List.Forall₂ (memAt S)
      ((vadd (mv (mat 128 z.fW) (layerNorm (row 128 z.ln2g) (row 128 z.ln2b) x)) (row 512 z.fB)).map gelu)
      ((affI 128 z.fW 512 z.fB (layerNormI (rowZ 128 z.ln2g) (rowZ 128 z.ln2b) Bin)).map geluI) :=
    f2_map (R := memAt S) (R' := memAt S) (f := gelu) (g := geluI) (fun _ _ h => memAt_gelu h)
      (f2_aff 128 z.fW 512 z.fB h2)
  have hid := f2_sub hidr hh
  have m : List.Forall₂ (memAt S) (mlpOut z.toLayer (layerNorm z.toLayer.ln2g z.toLayer.ln2b x))
      (affI 512 z.pW 128 z.pB Bhid) := by
    simp only [mlpOut, LayerZ.toLayer]
    exact f2_aff 512 z.pW 128 z.pB hid
  unfold stepC
  exact f2_sub (f2_vadd (f2_vadd hx a) m) ho


/-! ## The BOS-only prompt of pythia-14m -/

/-- The packed layers of pythia-14m. -/
def z0 : LayerZ := ⟨W.L0.ln1g, W.L0.ln1b, W.L0.ln2g, W.L0.ln2b, W.L0.qkvW, W.L0.qkvB, W.L0.oW, W.L0.oB, W.L0.fW, W.L0.fB, W.L0.pW, W.L0.pB⟩
def z1 : LayerZ := ⟨W.L1.ln1g, W.L1.ln1b, W.L1.ln2g, W.L1.ln2b, W.L1.qkvW, W.L1.qkvB, W.L1.oW, W.L1.oB, W.L1.fW, W.L1.fB, W.L1.pW, W.L1.pB⟩
def z2 : LayerZ := ⟨W.L2.ln1g, W.L2.ln1b, W.L2.ln2g, W.L2.ln2b, W.L2.qkvW, W.L2.qkvB, W.L2.oW, W.L2.oB, W.L2.fW, W.L2.fB, W.L2.pW, W.L2.pB⟩
def z3 : LayerZ := ⟨W.L3.ln1g, W.L3.ln1b, W.L3.ln2g, W.L3.ln2b, W.L3.qkvW, W.L3.qkvB, W.L3.oW, W.L3.oB, W.L3.fW, W.L3.fB, W.L3.pW, W.L3.pB⟩
def z4 : LayerZ := ⟨W.L4.ln1g, W.L4.ln1b, W.L4.ln2g, W.L4.ln2b, W.L4.qkvW, W.L4.qkvB, W.L4.oW, W.L4.oB, W.L4.fW, W.L4.fB, W.L4.pW, W.L4.pB⟩
def z5 : LayerZ := ⟨W.L5.ln1g, W.L5.ln1b, W.L5.ln2g, W.L5.ln2b, W.L5.qkvW, W.L5.qkvB, W.L5.oW, W.L5.oB, W.L5.fW, W.L5.fB, W.L5.pW, W.L5.pB⟩

/-- Packed row `t` of the input embedding / of the unembedding. -/
def eRowN (t : Nat) : Nat := (W.eChunks.getD (t / 256) []).getD (t % 256) 0
def uRowN (t : Nat) : Nat := (W.uChunks.getD (t / 256) []).getD (t % 256) 0

/-- Checks `lo / 10^6 ≤ 1 / (1 + exp (-(logit t1 - logit t0))) ≤ hi / 10^6` from a box `B` for the
residual stream after the last layer. -/
def probCheck (u0 u1 : Nat) (B : List Iv) (lo hi : Int) : Bool :=
  (probI (logitDiffI W.lnfg W.lnfb u0 u1 B)).ok &&
    decide (lo * S ≤ (probI (logitDiffI W.lnfg W.lnfb u0 u1 B)).lo * 1000000) &&
    decide ((probI (logitDiffI W.lnfg W.lnfb u0 u1 B)).hi * 1000000 ≤ hi * S)

/-- The candidate-renormalised probability of `t1` against `t0` after the one-token prompt `[t]`. -/
noncomputable def pred1 (θ : Params) (t t0 t1 : ℕ) : ℝ :=
  Real.exp (logit θ [t] t1) / (Real.exp (logit θ [t] t0) + Real.exp (logit θ [t] t1))

/-- **One-token certificate.** Eighteen kernel checks (three per layer) along boxes and a final check give
a six-digit enclosure of pythia-14m's two-way prediction after the one-token prompt `[t]`. -/
theorem pred1_encl (t t0 t1 : ℕ) (B1 B2 B3 B4 B5 B6 A0 A1 A2 A3 A4 A5 H0 H1 H2 H3 H4 H5 : List Iv)
    (lo hi : ℤ)
    (a0 : attCheck z0 (embI (eRowN t)) A0 = true) (g0 : hidCheck z0 (embI (eRowN t)) H0 = true)
    (o0 : outCheck z0 (embI (eRowN t)) A0 H0 B1 = true)
    (a1 : attCheck z1 B1 A1 = true) (g1 : hidCheck z1 B1 H1 = true) (o1 : outCheck z1 B1 A1 H1 B2 = true)
    (a2 : attCheck z2 B2 A2 = true) (g2 : hidCheck z2 B2 H2 = true) (o2 : outCheck z2 B2 A2 H2 B3 = true)
    (a3 : attCheck z3 B3 A3 = true) (g3 : hidCheck z3 B3 H3 = true) (o3 : outCheck z3 B3 A3 H3 B4 = true)
    (a4 : attCheck z4 B4 A4 = true) (g4 : hidCheck z4 B4 H4 = true) (o4 : outCheck z4 B4 A4 H4 B5 = true)
    (a5 : attCheck z5 B5 A5 = true) (g5 : hidCheck z5 B5 H5 = true) (o5 : outCheck z5 B5 A5 H5 B6 = true)
    (hf : probCheck (uRowN t0) (uRowN t1) B6 lo hi = true) :
    (lo : ℝ) / 10 ^ 6 ≤ pred1 pythia14m t t0 t1 ∧ pred1 pythia14m t t0 t1 ≤ (hi : ℝ) / 10 ^ 6 := by
  have e0 := f2_emb (eRowN t)
  have s1 := layer_ok3 z0 e0 a0 g0 o0
  have s2 := layer_ok3 z1 s1 a1 g1 o1
  have s3 := layer_ok3 z2 s2 a2 g2 o2
  have s4 := layer_ok3 z3 s3 a3 g3 o3
  have s5 := layer_ok3 z4 s4 a4 g4 o4
  have s6 := layer_ok3 z5 s5 a5 g5 o5
  have hd := memAt_prob (memAt_logitDiff W.lnfg W.lnfb (uRowN t0) (uRowN t1) s6)
  have hl : lastHidden pythia14m [t] = layerNorm (row 128 W.lnfg) (row 128 W.lnfb)
      (stepC z5.toLayer (stepC z4.toLayer (stepC z3.toLayer (stepC z2.toLayer (stepC z1.toLayer
        (stepC z0.toLayer (row 128 (eRowN t)))))))) := by
    rw [lastHidden_single]
    rfl
  have hp : pred1 pythia14m t t0 t1 =
      Real.exp (dot (row 128 (uRowN t1)) (layerNorm (row 128 W.lnfg) (row 128 W.lnfb)
        (stepC z5.toLayer (stepC z4.toLayer (stepC z3.toLayer (stepC z2.toLayer (stepC z1.toLayer
          (stepC z0.toLayer (row 128 (eRowN t)))))))))) /
      (Real.exp (dot (row 128 (uRowN t0)) (layerNorm (row 128 W.lnfg) (row 128 W.lnfb)
        (stepC z5.toLayer (stepC z4.toLayer (stepC z3.toLayer (stepC z2.toLayer (stepC z1.toLayer
          (stepC z0.toLayer (row 128 (eRowN t)))))))))) +
       Real.exp (dot (row 128 (uRowN t1)) (layerNorm (row 128 W.lnfg) (row 128 W.lnfb)
        (stepC z5.toLayer (stepC z4.toLayer (stepC z3.toLayer (stepC z2.toLayer (stepC z1.toLayer
          (stepC z0.toLayer (row 128 (eRowN t))))))))))) := by
    unfold pred1 logit
    rw [hl]
    rfl
  rw [hp]
  simp only [probCheck, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨hok, c1⟩, c2⟩ := hf
  obtain ⟨d1, d2⟩ := hd hok
  have hS := S_pos
  have c1' : (lo : ℝ) * S ≤ ((probI (logitDiffI W.lnfg W.lnfb (uRowN t0) (uRowN t1) B6)).lo : ℝ) * 1000000 := by
    exact_mod_cast c1
  have c2' : ((probI (logitDiffI W.lnfg W.lnfb (uRowN t0) (uRowN t1) B6)).hi : ℝ) * 1000000 ≤ (hi : ℝ) * S := by
    exact_mod_cast c2
  constructor
  · rw [div_le_iff₀ (by norm_num)]
    apply le_of_mul_le_mul_right _ hS
    exact le_trans c1' (le_trans (mul_le_mul_of_nonneg_right d1 (by norm_num : (0 : ℝ) ≤ 1000000))
      (le_of_eq (by ring)))
  · rw [le_div_iff₀ (by norm_num)]
    apply le_of_mul_le_mul_right _ hS
    exact le_trans (le_of_eq (by ring))
      (le_trans (mul_le_mul_of_nonneg_right d2 (by norm_num : (0 : ℝ) ≤ 1000000)) c2')


end CON
