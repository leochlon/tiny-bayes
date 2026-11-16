import Mathlib
import CON.PRO.Elem

/-! An interval enclosure of `π`, from Mathlib's bounds
`2^(n+1) √(2 - s_n) < π < 2^(n+1) √(2 - s_n) + 1/4^n`, `s_0 = 0`, `s_(k+1) = √(2 + s_k)`
(`Real.pi_gt_sqrtTwoAddSeries`, `Real.pi_lt_sqrtTwoAddSeries`), evaluated with the sound `sqrtI`. -/

namespace CON.PRO

/-- `2` at scale `S`. -/
def twoI : Iv := ⟨2 * S, 2 * S, true⟩

theorem memAt_two : memAt S (2 : ℝ) twoI := by
  intro _
  show ((2 * S : ℤ) : ℝ) ≤ 2 * S ∧ (2 : ℝ) * S ≤ ((2 * S : ℤ) : ℝ)
  push_cast
  exact ⟨le_refl _, le_refl _⟩

/-- Enclosure of `Real.sqrtTwoAddSeries 0 n`. -/
def staI : Nat → Iv
  | 0 => zero
  | n + 1 => sqrtI (add twoI (staI n))

theorem memAt_sta : ∀ n : ℕ, memAt S (Real.sqrtTwoAddSeries 0 n) (staI n)
  | 0 => by
    simp only [Real.sqrtTwoAddSeries, staI]
    exact memAt_zero S
  | n + 1 => by
    simp only [Real.sqrtTwoAddSeries, staI]
    exact memAt_sqrt (memAt_add memAt_two (memAt_sta n))

/-- Enclosure of `π` from `n` steps. -/
def piIn (n : Nat) : Iv :=
  add (mulZ (2 ^ (n + 1)) (sqrtI (add twoI (neg (staI n))))) ⟨0, cdiv S (4 ^ n), true⟩

theorem memAt_piIn (n : ℕ) : memAt S Real.pi (piIn n) := by
  have h1 := Real.pi_gt_sqrtTwoAddSeries n
  have h2 := Real.pi_lt_sqrtTwoAddSeries n
  have hr := memAt_mulZ (2 ^ (n + 1)) (memAt_sqrt (memAt_add memAt_two (memAt_neg (memAt_sta n))))
  have hδ : memAt S (Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n))
      ⟨0, cdiv S (4 ^ n), true⟩ := by
    intro _
    have hpos : (0 : ℝ) < 4 ^ n := by positivity
    have hc := le_cdiv_mul S (4 ^ n) (by positivity)
    push_cast at hc
    have d0 : 0 < Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) := by linarith
    have d1 : Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) < 1 / 4 ^ n := by linarith
    show ((0 : ℤ) : ℝ) ≤ (Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n)) * S ∧
      (Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n)) * S ≤ ((cdiv S (4 ^ n) : ℤ) : ℝ)
    constructor
    · have := (mul_pos d0 S_pos).le
      simpa using this
    · have t1 : (Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n)) * S ≤ 1 / 4 ^ n * S :=
        mul_le_mul_of_nonneg_right d1.le S_pos.le
      have e2 : 1 / (4 : ℝ) ^ n * S = S / 4 ^ n := by ring
      have t2 : (S : ℝ) / 4 ^ n ≤ ((cdiv S (4 ^ n) : ℤ) : ℝ) := by
        rw [div_le_iff₀ hpos]
        exact hc
      linarith
  have e : Real.pi = ((2 ^ (n + 1) : ℤ) : ℝ) * √(2 + -Real.sqrtTwoAddSeries 0 n) +
      (Real.pi - 2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n)) := by
    push_cast
    rw [← sub_eq_add_neg]
    ring
  have h := memAt_add hr hδ
  rw [← e] at h
  exact h

/-- Enclosure of `π` (70 steps: error below `4^-70` plus rounding). -/
def piI : Iv := piIn 70

theorem memAt_pi : memAt S Real.pi piI := memAt_piIn 70

end CON.PRO
