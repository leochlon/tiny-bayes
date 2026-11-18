import Mathlib

/-! # The equation `u' = -u + e^{-t}`, `u 0 = 1` on `[0, 4]`, and the exact error formula

`IsSolution u`: `u 0 = 1` and at every `t ∈ [0, 4]` the derivative of `u` within `[0, 4]` (one-sided at `0`
and at `4`) is `-u t + exp (-t)`.

For `e = u - M` and `r = M' + M - e^{-t}`, `(e^s e(s))' = -e^s r(s)`; the fundamental theorem of calculus
on `[0, t]` gives `u t - M t = e^{-t} (1 - M 0) - ∫₀ᵗ e^{-(t-s)} r s ds`. -/

namespace PINN

open Set MeasureTheory

/-- `u` solves `u' = -u + exp (-t)`, `u 0 = 1` on `[0, 4]`. -/
def IsSolution (u : ℝ → ℝ) : Prop :=
  u 0 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt u (-u t + Real.exp (-t)) (Icc 0 4) t

/-- The exact error formula for any `M` with a continuous derivative `M'` within `[0, 4]`. -/
theorem error_formula_core (M M' : ℝ → ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt M (M' t) (Icc 0 4) t)
    (hM' : ContinuousOn M' (Icc 0 4)) (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 4) :
    u t - M t = Real.exp (-t) * (1 - M 0) -
      ∫ s in (0 : ℝ)..t, Real.exp (-(t - s)) * (M' s + M s - Real.exp (-s)) := by
  have hFd : ∀ s ∈ Icc (0 : ℝ) 4, HasDerivWithinAt (fun y => Real.exp y * (u y - M y))
      (-(Real.exp s * (M' s + M s - Real.exp (-s)))) (Icc 0 4) s := by
    intro s hs
    have h := ((Real.hasDerivAt_exp s).hasDerivWithinAt (s := Icc (0 : ℝ) 4)).mul
      ((hu.2 s hs).sub (hM s hs))
    have e : -(Real.exp s * (M' s + M s - Real.exp (-s))) =
        Real.exp s * (u s - M s) + Real.exp s * ((-u s + Real.exp (-s)) - M' s) := by ring
    rw [e]
    exact h
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 4 := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun y => Real.exp y * (u y - M y)) (Icc 0 t) :=
    fun s hs => ((hFd s (hsub hs)).continuousWithinAt).mono hsub
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t, HasDerivAt (fun y => Real.exp y * (u y - M y))
      (-(Real.exp x * (M' x + M x - Real.exp (-x)))) x := by
    intro x hx
    have hx4 : x ∈ Ioo (0 : ℝ) 4 := ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
    exact (hFd x (Ioo_subset_Icc_self hx4)).hasDerivAt (Icc_mem_nhds hx4.1 hx4.2)
  have hMc : ContinuousOn M (Icc 0 4) := fun s hs => (hM s hs).continuousWithinAt
  have hEc : ContinuousOn (fun s : ℝ => Real.exp (-s)) (Icc 0 4) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn
  have hrc : ContinuousOn (fun s => M' s + M s - Real.exp (-s)) (Icc 0 4) := (hM'.add hMc).sub hEc
  have hF'c : ContinuousOn (fun s => -(Real.exp s * (M' s + M s - Real.exp (-s)))) (Icc 0 4) :=
    (Real.continuous_exp.continuousOn.mul hrc).neg
  have hint : IntervalIntegrable (fun s => -(Real.exp s * (M' s + M s - Real.exp (-s)))) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hF'c.mono hsub
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun y => Real.exp y * (u y - M y))
    (f' := fun s => -(Real.exp s * (M' s + M s - Real.exp (-s)))) ht.1 hcont hderiv hint
  rw [intervalIntegral.integral_neg] at hftc
  simp only [Real.exp_zero, one_mul, hu.1] at hftc
  have hI : (∫ s in (0 : ℝ)..t, Real.exp (-(t - s)) * (M' s + M s - Real.exp (-s))) =
      Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * (M' s + M s - Real.exp (-s)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    rw [show -(t - s) = -t + s by ring, Real.exp_add]
    ring
  rw [hI]
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp t * (u t - M t) =
      (1 - M 0) - ∫ s in (0 : ℝ)..t, Real.exp s * (M' s + M s - Real.exp (-s)) := by linarith
  have h3 : u t - M t = Real.exp (-t) * (Real.exp t * (u t - M t)) := by
    rw [← mul_assoc, hexp, one_mul]
  rw [h3, h2]
  ring

/-- The exact solution `(1 + t) e^{-t}` and its derivative `-t e^{-t}`. -/
theorem hasDerivAt_sol (t : ℝ) :
    HasDerivAt (fun x => (1 + x) * Real.exp (-x)) (-(t * Real.exp (-t))) t := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := (hasDerivAt_neg t).exp
  have h := h1.mul h2
  have e : -(t * Real.exp (-t)) = 1 * Real.exp (-t) + (1 + t) * (Real.exp (-t) * -1) := by ring
  rw [e]
  exact h

/-- `(1 + t) e^{-t}` is a solution. -/
theorem sol_isSolution : IsSolution (fun t => (1 + t) * Real.exp (-t)) := by
  refine ⟨by simp, fun t _ => ?_⟩
  have e : -((1 + t) * Real.exp (-t)) + Real.exp (-t) = -(t * Real.exp (-t)) := by ring
  rw [e]
  exact (hasDerivAt_sol t).hasDerivWithinAt


/-! ## The residual-sum bound -/

/-- `w(x, y, t) = ∫ e^{-(t - s)} ds` over `s ∈ [x, y] ∩ [0, t]` (set integral, Lebesgue measure). -/
noncomputable def wInt (x y t : ℝ) : ℝ := ∫ s in Icc x y ∩ Icc 0 t, Real.exp (-(t - s))

/-- The weight of piece `k` of the partition `a`: `w_k(t) = ∫_{[a_k, a_{k+1}] ∩ [0, t]} e^{-(t - s)} ds`. -/
noncomputable def wk (a : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := ∫ s in Icc (a k) (a (k + 1)) ∩ Icc 0 t, Real.exp (-(t - s))

theorem hasDerivAt_emts (t s : ℝ) : HasDerivAt (fun y => Real.exp (-(t - y))) (Real.exp (-(t - s))) s := by
  have h : HasDerivAt (fun y : ℝ => -(t - y)) 1 s :=
    ((hasDerivAt_id' s).const_sub t).neg.congr_deriv (neg_neg 1)
  have h2 := h.exp
  rw [mul_one] at h2
  exact h2

theorem integral_emts (t x y : ℝ) :
    ∫ s in x..y, Real.exp (-(t - s)) = Real.exp (-(t - y)) - Real.exp (-(t - x)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_emts t s)
  apply Continuous.intervalIntegrable
  fun_prop

/-- For `0 ≤ x ≤ y` the weight is the interval integral from `min x t` to `min y t`. -/
theorem wInt_eq (x y t : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    wInt x y t = ∫ s in (min x t)..(min y t), Real.exp (-(t - s)) := by
  have hset : Icc x y ∩ Icc 0 t = Icc x (min y t) := by
    ext s
    simp only [mem_inter_iff, mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩
      exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩
      exact ⟨⟨h1, h2⟩, le_trans hx h1, h4⟩
  unfold wInt
  rw [hset]
  by_cases hxt : x ≤ t
  · rw [min_eq_left hxt, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_min hxy hxt)]
  · push_neg at hxt
    have h2 : min y t = t := min_eq_right (le_trans hxt.le hxy)
    rw [min_eq_right hxt.le, h2, intervalIntegral.integral_same, Icc_eq_empty (not_le.mpr hxt), setIntegral_empty]

/-- Closed form of the weight. -/
theorem wInt_formula (x y t : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    wInt x y t = Real.exp (-(t - min y t)) - Real.exp (-(t - min x t)) := by
  rw [wInt_eq x y t hx hxy, integral_emts]

theorem wInt_nonneg (x y t : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : 0 ≤ wInt x y t := by
  rw [wInt_formula x y t hx hxy, sub_nonneg, Real.exp_le_exp]
  have : min x t ≤ min y t := min_le_min_right t hxy
  linarith

/-- The residual-sum bound for any `M` with a continuous derivative `M'` within `[0, 4]`. -/
theorem residual_sum_bound (M M' : ℝ → ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt M (M' t) (Icc 0 4) t)
    (hM' : ContinuousOn M' (Icc 0 4)) (K : ℕ) (a lo hi : ℕ → ℝ) (ha0 : a 0 = 0) (haK : a K = 4)
    (hmono : ∀ k < K, a k < a (k + 1))
    (hr : ∀ k < K, ∀ s ∈ Icc (a k) (a (k + 1)),
      lo k ≤ M' s + M s - Real.exp (-s) ∧ M' s + M s - Real.exp (-s) ≤ hi k)
    (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, hi k * wk a k t ≤ u t - M t ∧
      u t - M t ≤ Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, lo k * wk a k t := by
  have hform := error_formula_core M M' hM hM' u hu t ht
  have hle : ∀ i j, i ≤ j → j ≤ K → a i ≤ a j := by
    intro i j hij hjK
    induction j with
    | zero =>
      have : i = 0 := by omega
      rw [this]
    | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · have h1 := ih (by omega) (by omega)
        have h2 := hmono n (by omega)
        linarith
      · have : i = n + 1 := by omega
        rw [this]
  have ha_nonneg : ∀ k ≤ K, 0 ≤ a k := fun k hk => by
    have := hle 0 k (Nat.zero_le k) hk
    rwa [ha0] at this
  have ha_le : ∀ k ≤ K, a k ≤ 4 := fun k hk => by
    have := hle k K hk le_rfl
    rwa [haK] at this
  set f : ℝ → ℝ := fun s => Real.exp (-(t - s)) * (M' s + M s - Real.exp (-s)) with hf
  have hMc : ContinuousOn M (Icc 0 4) := fun s hs => (hM s hs).continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 4) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.exp (-(t - s))) (Icc 0 4) := by
      apply Continuous.continuousOn
      fun_prop
    have h2 : ContinuousOn (fun s : ℝ => Real.exp (-s)) (Icc 0 4) := by
      apply Continuous.continuousOn
      fun_prop
    exact h1.mul ((hM'.add hMc).sub h2)
  set c : ℕ → ℝ := fun k => min (a k) t with hc
  have hc_mem : ∀ k ≤ K, c k ∈ Icc (0 : ℝ) 4 := fun k hk =>
    ⟨le_min (ha_nonneg k hk) ht.1, le_trans (min_le_right _ _) ht.2⟩
  have hint : ∀ k < K, IntervalIntegrable f MeasureTheory.volume (c k) (c (k + 1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    exact hfc.mono (uIcc_subset_Icc (hc_mem k hk.le) (hc_mem (k + 1) hk))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hc0 : c 0 = 0 := by simp only [hc, ha0]; exact min_eq_left ht.1
  have hcK : c K = t := by simp only [hc, haK]; exact min_eq_right ht.2
  rw [hc0, hcK] at hsum
  have hw : ∀ k < K, wk a k t = ∫ s in (c k)..(c (k + 1)), Real.exp (-(t - s)) := fun k hk =>
    wInt_eq (a k) (a (k + 1)) t (ha_nonneg k hk.le) (hmono k hk).le
  have hpiece : ∀ k < K, lo k * wk a k t ≤ ∫ s in (c k)..(c (k + 1)), f s ∧
      ∫ s in (c k)..(c (k + 1)), f s ≤ hi k * wk a k t := by
    intro k hk
    rw [hw k hk, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    by_cases hkt : a k ≤ t
    · have hck : c k = a k := min_eq_left hkt
      have hcc : c k ≤ c (k + 1) := min_le_min_right t (hmono k hk).le
      have hsub : ∀ s ∈ Icc (c k) (c (k + 1)), s ∈ Icc (a k) (a (k + 1)) := fun s hs =>
        ⟨by rw [← hck]; exact hs.1, le_trans hs.2 (min_le_left _ _)⟩
      have hE : IntervalIntegrable (fun s => Real.exp (-(t - s))) MeasureTheory.volume (c k) (c (k + 1)) := by
        apply Continuous.intervalIntegrable
        fun_prop
      constructor
      · apply intervalIntegral.integral_mono_on hcc (hE.const_mul (lo k)) (hint k hk)
        intro s hs
        have := (hr k hk s (hsub s hs)).1
        have hp := Real.exp_pos (-(t - s))
        simp only [hf]
        nlinarith
      · apply intervalIntegral.integral_mono_on hcc (hint k hk) (hE.const_mul (hi k))
        intro s hs
        have := (hr k hk s (hsub s hs)).2
        have hp := Real.exp_pos (-(t - s))
        simp only [hf]
        nlinarith
    · push_neg at hkt
      have h1 : c k = t := min_eq_right hkt.le
      have h2 : c (k + 1) = t := min_eq_right (le_trans hkt.le (hmono k hk).le)
      rw [h1, h2, intervalIntegral.integral_same, intervalIntegral.integral_same, intervalIntegral.integral_same]
      exact ⟨le_rfl, le_rfl⟩
  have hlo : ∑ k ∈ Finset.range K, lo k * wk a k t ≤ ∫ s in (0 : ℝ)..t, f s := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro k hk
    exact (hpiece k (Finset.mem_range.mp hk)).1
  have hhi : ∫ s in (0 : ℝ)..t, f s ≤ ∑ k ∈ Finset.range K, hi k * wk a k t := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro k hk
    exact (hpiece k (Finset.mem_range.mp hk)).2
  have hform' : u t - M t = Real.exp (-t) * (1 - M 0) - ∫ s in (0 : ℝ)..t, f s := hform
  constructor <;> linarith

end PINN
