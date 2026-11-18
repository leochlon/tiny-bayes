import Mathlib

/-! # A verified enclosure of the Gaussian integral

`gaussInt x = ∫_0^x exp (-t^2/2) dt`, so that the normal distribution function is
`Phi x = 1/2 + gaussInt x / sqrt (2 pi)`. With `gser N x = Σ_{n<N} x^(2n+1) / (2n+1)!!`
(the partial sums of `exp (x^2/2) * gaussInt x`) and `dco N = 1 / (2N-1)!!`:

    exp (-x^2/2) * (gser N x + min 0 R) ≤ gaussInt x ≤ exp (-x^2/2) * (gser N x + max 0 R),
    R = dco N / N * x^(2N+1),        whenever 1 ≤ N and x^2 ≤ N + 1.

Proof: both differences vanish at 0 and have a derivative of constant sign. -/

namespace CON

noncomputable section

/-- `∫_0^x exp (-t^2/2) dt`. -/
def gaussInt (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)

/-- `dco N = 1 / (2N-1)!!`. -/
def dco : ℕ → ℝ
  | 0 => 1
  | N + 1 => dco N / (2 * (N : ℝ) + 1)

/-- `gser N x = Σ_{n<N} x^(2n+1) / (2n+1)!!`. -/
def gser : ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, x => gser N x + dco (N + 1) * x ^ (2 * N + 1)

end

theorem dco_pos : ∀ N : ℕ, 0 < dco N
  | 0 => by simp [dco]
  | N + 1 => by
    have h := dco_pos N
    simp only [dco]
    positivity

theorem gser_zero : ∀ N : ℕ, gser N 0 = 0
  | 0 => rfl
  | N + 1 => by simp [gser, gser_zero N]

theorem gaussInt_zero : gaussInt 0 = 0 := by simp [gaussInt]

theorem hasDerivAt_gser : ∀ (N : ℕ) (x : ℝ),
    HasDerivAt (gser N) (1 + x * gser N x - dco N * x ^ (2 * N)) x
  | 0, x => by
    have e : gser 0 = fun _ => (0 : ℝ) := by funext y; rfl
    rw [e]
    exact (hasDerivAt_const x (0 : ℝ)).congr_deriv (by simp [dco])
  | N + 1, x => by
    have ih := hasDerivAt_gser N x
    have h1 := (hasDerivAt_pow (2 * N + 1) x).const_mul (dco (N + 1))
    have h2 : HasDerivAt (fun y => gser N y + dco (N + 1) * y ^ (2 * N + 1)) _ x := ih.add h1
    have e : gser (N + 1) = fun y => gser N y + dco (N + 1) * y ^ (2 * N + 1) := by funext y; rfl
    rw [e]
    refine h2.congr_deriv ?_
    have hne : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    simp only [dco, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem hasDerivAt_gaussInt (x : ℝ) : HasDerivAt gaussInt (Real.exp (-(x ^ 2) / 2)) x := by
  have hc : Continuous fun t : ℝ => Real.exp (-(t ^ 2) / 2) := by fun_prop
  exact (hc.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_expNegSq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) (Real.exp (-(x ^ 2) / 2) * (-x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    have h : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) _ x := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine h.congr_deriv ?_
    simp
    ring
  exact h1.exp

theorem gauss_lower_deriv (N : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => gaussInt x - Real.exp (-(x ^ 2) / 2) * gser N x)
      (Real.exp (-(x ^ 2) / 2) * (dco N * x ^ (2 * N))) x := by
  have h : HasDerivAt (fun x : ℝ => gaussInt x - Real.exp (-(x ^ 2) / 2) * gser N x) _ x :=
    (hasDerivAt_gaussInt x).sub ((hasDerivAt_expNegSq x).mul (hasDerivAt_gser N x))
  refine h.congr_deriv ?_
  ring

theorem gauss_lower_mono (N : ℕ) :
    Monotone fun x : ℝ => gaussInt x - Real.exp (-(x ^ 2) / 2) * gser N x := by
  apply monotone_of_deriv_nonneg (fun x => (gauss_lower_deriv N x).differentiableAt)
  intro x
  rw [(gauss_lower_deriv N x).deriv]
  have h3 : 0 ≤ x ^ (2 * N) := by rw [pow_mul]; positivity
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (dco_pos N).le h3)

theorem gauss_upper_deriv (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * (gser N x + dco N / (N : ℝ) * x ^ (2 * N + 1)) - gaussInt x)
      (Real.exp (-(x ^ 2) / 2) * (dco N / (N : ℝ) * x ^ (2 * N) * ((N : ℝ) + 1 - x ^ 2))) x := by
  have hp := (hasDerivAt_pow (2 * N + 1) x).const_mul (dco N / (N : ℝ))
  have hs : HasDerivAt (fun y => gser N y + dco N / (N : ℝ) * y ^ (2 * N + 1)) _ x :=
    (hasDerivAt_gser N x).add hp
  have h : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * (gser N x + dco N / (N : ℝ) * x ^ (2 * N + 1)) - gaussInt x) _ x :=
    ((hasDerivAt_expNegSq x).mul hs).sub (hasDerivAt_gaussInt x)
  refine h.congr_deriv ?_
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **Enclosure of the Gaussian integral** by the positive series with an explicit remainder. -/
theorem gaussInt_encl (N : ℕ) (hN : 1 ≤ N) (x : ℝ) (hx : x ^ 2 ≤ (N : ℝ) + 1) :
    Real.exp (-(x ^ 2) / 2) * (gser N x + min 0 (dco N / (N : ℝ) * x ^ (2 * N + 1))) ≤ gaussInt x ∧
      gaussInt x ≤ Real.exp (-(x ^ 2) / 2) * (gser N x + max 0 (dco N / (N : ℝ) * x ^ (2 * N + 1))) := by
  have hA := gauss_lower_mono N
  have hB : MonotoneOn (fun y : ℝ => Real.exp (-(y ^ 2) / 2) *
      (gser N y + dco N / (N : ℝ) * y ^ (2 * N + 1)) - gaussInt y) (Set.Icc (-|x|) |x|) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun y _ => (gauss_upper_deriv N hN y).continuousAt.continuousWithinAt
    · exact fun y _ => (gauss_upper_deriv N hN y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(gauss_upper_deriv N hN y).deriv]
      have hy2 : y ^ 2 ≤ x ^ 2 := sq_le_sq.mpr (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
      have h2 : 0 ≤ dco N / (N : ℝ) := div_nonneg (dco_pos N).le (Nat.cast_nonneg N)
      have h3 : 0 ≤ y ^ (2 * N) := by rw [pow_mul]; positivity
      have h4 : 0 ≤ (N : ℝ) + 1 - y ^ 2 := by linarith
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg h2 h3) h4)
  have g0 := gaussInt_zero
  have s0 := gser_zero N
  have z : (0 : ℝ) ^ (2 * N + 1) = 0 := by simp
  have hc : 0 ≤ dco N / (N : ℝ) := div_nonneg (dco_pos N).le (Nat.cast_nonneg N)
  have m0 : (0 : ℝ) ∈ Set.Icc (-|x|) |x| := ⟨neg_nonpos.mpr (abs_nonneg x), abs_nonneg x⟩
  have mx : x ∈ Set.Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
  rcases le_total 0 x with h0 | h0
  · have a : gaussInt 0 - Real.exp (-((0 : ℝ) ^ 2) / 2) * gser N 0 ≤
        gaussInt x - Real.exp (-(x ^ 2) / 2) * gser N x := hA h0
    have b : Real.exp (-((0 : ℝ) ^ 2) / 2) * (gser N 0 + dco N / (N : ℝ) * (0 : ℝ) ^ (2 * N + 1)) - gaussInt 0 ≤
        Real.exp (-(x ^ 2) / 2) * (gser N x + dco N / (N : ℝ) * x ^ (2 * N + 1)) - gaussInt x := hB m0 mx h0
    rw [g0, s0] at a
    rw [g0, s0, z] at b
    have hR : 0 ≤ dco N / (N : ℝ) * x ^ (2 * N + 1) := mul_nonneg hc (pow_nonneg h0 _)
    rw [min_eq_left hR, max_eq_right hR]
    constructor <;> linarith
  · have a : gaussInt x - Real.exp (-(x ^ 2) / 2) * gser N x ≤
        gaussInt 0 - Real.exp (-((0 : ℝ) ^ 2) / 2) * gser N 0 := hA h0
    have b : Real.exp (-(x ^ 2) / 2) * (gser N x + dco N / (N : ℝ) * x ^ (2 * N + 1)) - gaussInt x ≤
        Real.exp (-((0 : ℝ) ^ 2) / 2) * (gser N 0 + dco N / (N : ℝ) * (0 : ℝ) ^ (2 * N + 1)) - gaussInt 0 := hB mx m0 h0
    rw [g0, s0] at a
    rw [g0, s0, z] at b
    have hR : dco N / (N : ℝ) * x ^ (2 * N + 1) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hc, Odd.pow_nonpos ⟨N, rfl⟩ h0⟩)
    rw [min_eq_right hR, max_eq_left hR]
    constructor <;> linarith

/-- The Gaussian integral is odd. -/
theorem gaussInt_neg (x : ℝ) : gaussInt (-x) = -gaussInt x := by
  unfold gaussInt
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
  simp only [neg_sq, neg_zero] at h
  rw [h, intervalIntegral.integral_symm (-x) 0]

/-- The Gaussian integral is increasing. -/
theorem gaussInt_mono : Monotone gaussInt := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_gaussInt x).differentiableAt)
  intro x
  rw [(hasDerivAt_gaussInt x).deriv]
  exact (Real.exp_pos _).le

/-- **Tail.** Beyond `a ≥ 0` the Gaussian integral grows by at most `(x - a) * exp (-a^2/2)`. -/
theorem gaussInt_tail (a x : ℝ) (ha : 0 ≤ a) (hx : a ≤ x) :
    gaussInt x ≤ gaussInt a + (x - a) * Real.exp (-(a ^ 2) / 2) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => gaussInt a + (y - a) * Real.exp (-(a ^ 2) / 2) - gaussInt y)
      (Real.exp (-(a ^ 2) / 2) - Real.exp (-(y ^ 2) / 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => gaussInt a + (y - a) * Real.exp (-(a ^ 2) / 2))
        (Real.exp (-(a ^ 2) / 2)) y := by
      have h := (((hasDerivAt_id y).sub_const a).mul_const (Real.exp (-(a ^ 2) / 2))).const_add (gaussInt a)
      refine h.congr_deriv ?_
      simp
    exact h1.sub (hasDerivAt_gaussInt y)
  have hm : MonotoneOn (fun y : ℝ => gaussInt a + (y - a) * Real.exp (-(a ^ 2) / 2) - gaussInt y)
      (Set.Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      have hy' : a < y := hy
      have h2 : a ^ 2 ≤ y ^ 2 := by nlinarith
      have h3 : Real.exp (-(y ^ 2) / 2) ≤ Real.exp (-(a ^ 2) / 2) := Real.exp_le_exp.mpr (by linarith)
      linarith
  have h := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have e : gaussInt a + (a - a) * Real.exp (-(a ^ 2) / 2) - gaussInt a ≤
      gaussInt a + (x - a) * Real.exp (-(a ^ 2) / 2) - gaussInt x := h
  nlinarith [e]


end CON
