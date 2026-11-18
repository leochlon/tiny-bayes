import Mathlib
import CON.PRO.Interval

/-! # Soundness of the interval operations over `ℝ`

`memAt s x X` says that the interval `X` encloses the real `x` at scale `s`. Each operation of
`PRO.Interval` maps enclosures to enclosures. -/

namespace CON.PRO

/-- `X` encloses `x` at scale `s`. -/
def memAt (s x : ℝ) (X : Iv) : Prop := X.ok = true → (X.lo : ℝ) ≤ x * s ∧ x * s ≤ X.hi

theorem S_pos_int : (0 : ℤ) < S := by decide

theorem S_pos : (0 : ℝ) < S := by exact_mod_cast S_pos_int

theorem S_eq : S = 16777216 * S76 := by decide

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
  have e : (S : ℝ) = 16777216 * S76 := by exact_mod_cast S_eq
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

end CON.PRO
