import Mathlib
import PINN.Wts

/-! # The networks over `ℝ` and their derivatives

`net P t = Σⱼ W3[j] tanh (Σᵢ W2[j][i] tanh (W1[i] t + b1[i]) + b2[j]) + b3`, every weight the integer of `P`
divided by `2^16`, sums over `i, j = 0, …, 31`. `N = net WN`, `Ñ = net WH`, `û t = 1 + t Ñ t`. -/

namespace PINN

open Finset

/-- The weight with integer numerator `z`: `z / 2^16`. -/
noncomputable def w (z : ℤ) : ℝ := (z : ℝ) / 65536

/-- First-layer pre-activation `W1[i] t + b1[i]`. -/
noncomputable def z1 (P : Wts) (i : ℕ) (t : ℝ) : ℝ := w (P.w1.getD i 0) * t + w (P.c1.getD i 0)

/-- Second-layer pre-activation `Σᵢ W2[j][i] tanh (W1[i] t + b1[i]) + b2[j]`. -/
noncomputable def z2 (P : Wts) (j : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * Real.tanh (z1 P i t) + w (P.c2.getD j 0)

/-- The network: `Σⱼ W3[j] tanh (z2 j t) + b3`. -/
noncomputable def net (P : Wts) (t : ℝ) : ℝ := ∑ j ∈ range 32, w (P.w3.getD j 0) * Real.tanh (z2 P j t) + w P.c3

/-- Derivative of `z2 j`. -/
noncomputable def dz2 (P : Wts) (j : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * (w (P.w1.getD i 0) * (1 - Real.tanh (z1 P i t) ^ 2))

/-- Derivative of the network. -/
noncomputable def dnet (P : Wts) (t : ℝ) : ℝ :=
  ∑ j ∈ range 32, w (P.w3.getD j 0) * ((1 - Real.tanh (z2 P j t) ^ 2) * dz2 P j t)

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) hc
  have e : (fun y => Real.sinh y / Real.cosh y) = Real.tanh := by
    funext y
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  have e2 : 1 - Real.tanh x ^ 2 = (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [e2]
  exact h

theorem hasDerivAt_z1 (P : Wts) (i : ℕ) (t : ℝ) : HasDerivAt (z1 P i) (w (P.w1.getD i 0)) t := by
  have h := ((hasDerivAt_id t).const_mul (w (P.w1.getD i 0))).add_const (w (P.c1.getD i 0))
  rw [mul_one] at h
  exact h

theorem hasDerivAt_z2 (P : Wts) (j : ℕ) (t : ℝ) : HasDerivAt (z2 P j) (dz2 P j t) t := by
  have h : HasDerivAt (fun y => ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * Real.tanh (z1 P i y))
      (∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * ((1 - Real.tanh (z1 P i t) ^ 2) * w (P.w1.getD i 0))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hasDerivAt_tanh (z1 P i t)).comp t (hasDerivAt_z1 P i t)).const_mul _
  have h2 := h.add_const (w (P.c2.getD j 0))
  have e : dz2 P j t = ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) *
      ((1 - Real.tanh (z1 P i t) ^ 2) * w (P.w1.getD i 0)) := by
    unfold dz2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e]
  exact h2

theorem hasDerivAt_net (P : Wts) (t : ℝ) : HasDerivAt (net P) (dnet P t) t := by
  have h : HasDerivAt (fun y => ∑ j ∈ range 32, w (P.w3.getD j 0) * Real.tanh (z2 P j y))
      (∑ j ∈ range 32, w (P.w3.getD j 0) * ((1 - Real.tanh (z2 P j t) ^ 2) * dz2 P j t)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hasDerivAt_tanh (z2 P j t)).comp t (hasDerivAt_z2 P j t)).const_mul _
  exact h.add_const (w P.c3)

/-- The network `N` of `data/net.json`. -/
noncomputable def N (t : ℝ) : ℝ := net WN t

/-- The network `Ñ` of `data/net_hardic.json`. -/
noncomputable def Nh (t : ℝ) : ℝ := net WH t

/-- The model with the initial condition built in: `û t = 1 + t Ñ t`. -/
noncomputable def uhat (t : ℝ) : ℝ := 1 + t * Nh t

/-- `W1[i]^2 tanh (z1 i) (1 - tanh (z1 i)^2)`. -/
noncomputable def q1 (P : Wts) (i : ℕ) (t : ℝ) : ℝ :=
  w (P.w1.getD i 0) * (w (P.w1.getD i 0) * (Real.tanh (z1 P i t) * (1 - Real.tanh (z1 P i t) ^ 2)))

/-- `Σᵢ W2[j][i] q1 i`, so that the second derivative of `z2 j` is `-2 dd2 j`. -/
noncomputable def dd2 (P : Wts) (j : ℕ) (t : ℝ) : ℝ := ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * q1 P i t

/-- Second derivative of the network. -/
noncomputable def d2net (P : Wts) (t : ℝ) : ℝ :=
  -2 * ∑ j ∈ range 32, w (P.w3.getD j 0) *
    ((1 - Real.tanh (z2 P j t) ^ 2) * (dd2 P j t + Real.tanh (z2 P j t) * dz2 P j t ^ 2))

theorem hasDerivAt_dz2 (P : Wts) (j : ℕ) (t : ℝ) : HasDerivAt (dz2 P j) (-2 * dd2 P j t) t := by
  have h : HasDerivAt (fun y => ∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) *
      (w (P.w1.getD i 0) * (1 - Real.tanh (z1 P i y) ^ 2)))
      (∑ i ∈ range 32, w ((P.w2.getD j []).getD i 0) * (w (P.w1.getD i 0) *
        -(((2 : ℕ) : ℝ) * Real.tanh (z1 P i t) ^ (2 - 1) *
          ((1 - Real.tanh (z1 P i t) ^ 2) * w (P.w1.getD i 0))))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (((((hasDerivAt_tanh (z1 P i t)).comp t (hasDerivAt_z1 P i t)).fun_pow 2).const_sub 1).const_mul
      (w (P.w1.getD i 0))).const_mul _
  apply h.congr_deriv
  unfold dd2 q1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem hasDerivAt_dnet (P : Wts) (t : ℝ) : HasDerivAt (dnet P) (d2net P t) t := by
  have h : HasDerivAt (fun y => ∑ j ∈ range 32, w (P.w3.getD j 0) * ((1 - Real.tanh (z2 P j y) ^ 2) * dz2 P j y))
      (∑ j ∈ range 32, w (P.w3.getD j 0) *
        (-(((2 : ℕ) : ℝ) * Real.tanh (z2 P j t) ^ (2 - 1) * ((1 - Real.tanh (z2 P j t) ^ 2) * dz2 P j t)) *
          dz2 P j t + (1 - Real.tanh (z2 P j t) ^ 2) * (-2 * dd2 P j t))) t := by
    apply HasDerivAt.fun_sum
    intro j _
    exact (((((hasDerivAt_tanh (z2 P j t)).comp t (hasDerivAt_z2 P j t)).fun_pow 2).const_sub 1).mul
      (hasDerivAt_dz2 P j t)).const_mul _
  apply h.congr_deriv
  unfold d2net
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem continuous_dnet (P : Wts) : Continuous (dnet P) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_dnet P t).continuousAt

theorem continuous_net (P : Wts) : Continuous (net P) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_net P t).continuousAt

/-- Residual of `N` with its derivative written out: `N' + N - e^{-t}`. -/
noncomputable def rN (t : ℝ) : ℝ := dnet WN t + net WN t - Real.exp (-t)

noncomputable def rN' (t : ℝ) : ℝ := d2net WN t + dnet WN t + Real.exp (-t)

/-- Residual of `û`: `û' + û - e^{-t}` with `û' = Ñ + t Ñ'`. -/
noncomputable def rH (t : ℝ) : ℝ := (net WH t + t * dnet WH t) + (1 + t * net WH t) - Real.exp (-t)

noncomputable def rH' (t : ℝ) : ℝ :=
  (2 * dnet WH t + t * d2net WH t) + (net WH t + t * dnet WH t) + Real.exp (-t)

theorem hasDerivAt_emt (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := (hasDerivAt_neg t).exp
  apply h.congr_deriv
  ring

theorem hasDerivAt_rN (t : ℝ) : HasDerivAt rN (rN' t) t := by
  have h := ((hasDerivAt_dnet WN t).add (hasDerivAt_net WN t)).sub (hasDerivAt_emt t)
  apply h.congr_deriv
  unfold rN'
  ring

theorem hasDerivAt_rH (t : ℝ) : HasDerivAt rH (rH' t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x * dnet WH x) (1 * dnet WH t + t * d2net WH t) t :=
    (hasDerivAt_id' t).mul (hasDerivAt_dnet WH t)
  have h2 : HasDerivAt (fun x : ℝ => x * net WH x) (1 * net WH t + t * dnet WH t) t :=
    (hasDerivAt_id' t).mul (hasDerivAt_net WH t)
  have h := (((hasDerivAt_net WH t).add h1).add (h2.const_add 1)).sub (hasDerivAt_emt t)
  apply h.congr_deriv
  unfold rH'
  ring

/-- `û' = Ñ + t Ñ'` everywhere. -/
theorem hasDerivAt_uhat (t : ℝ) : HasDerivAt uhat (net WH t + t * dnet WH t) t := by
  have h : HasDerivAt (fun x : ℝ => x * net WH x) (1 * net WH t + t * dnet WH t) t :=
    (hasDerivAt_id' t).mul (hasDerivAt_net WH t)
  apply (h.const_add 1).congr_deriv
  ring

theorem hasDerivAt_N (t : ℝ) : HasDerivAt N (dnet WN t) t := hasDerivAt_net WN t

end PINN
