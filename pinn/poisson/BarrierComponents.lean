import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Elementary quartic barrier components only. This file does NOT prove
the maximum principle, a Poisson transfer theorem, or any network bound. -/
namespace PoissonPilot
noncomputable def p (x : ℝ) : ℝ := x * (1-x)
noncomputable def dp (x : ℝ) : ℝ := 1-2*x
noncomputable def B (x y : ℝ) : ℝ :=
  (p x + p y)/20 - ((p x)^2+(p y)^2)/5 + 6*p x*p y/5
noncomputable def Bx (x y : ℝ) : ℝ :=
  dp x * ((1:ℝ)/20 - 2*p x/5 + 6*p y/5)
noncomputable def Bxx (x y : ℝ) : ℝ :=
  -2 * ((1:ℝ)/20 - 2*p x/5 + 6*p y/5) - 2*(dp x)^2/5

theorem p_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ p x := by
  exact mul_nonneg h0 (sub_nonneg.mpr h1)

theorem p_le (x : ℝ) : p x ≤ (1:ℝ)/4 := by
  dsimp [p]
  nlinarith [sq_nonneg (x - (1:ℝ)/2)]

theorem barrier_nonneg {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ B x y := by
  have hp := p_nonneg hx0 hx1
  have hq := p_nonneg hy0 hy1
  have hpp := p_le x
  have hqq := p_le y
  have h1 := mul_nonneg hp (show 0 ≤ 1-4*p x by linarith)
  have h2 := mul_nonneg hq (show 0 ≤ 1-4*p y by linarith)
  have h3 := mul_nonneg hp hq
  dsimp [B]
  nlinarith

theorem barrier_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : B x y ≤ (3:ℝ)/40 := by
  have hp := p_nonneg hx0 hx1
  have hq := p_nonneg hy0 hy1
  have hpp := p_le x
  have hqq := p_le y
  have hs0 : 0 ≤ p x + p y := by linarith
  have hs1 : p x + p y ≤ (1:ℝ)/2 := by linarith
  have hh := mul_nonneg (show 0 ≤ (1:ℝ)/2 - (p x+p y) by linarith)
    (show 0 ≤ (3:ℝ)/20 + (p x+p y)/5 by positivity)
  have hd := sq_nonneg (p x-p y)
  dsimp [B]
  nlinarith

theorem hasDerivAt_p (x : ℝ) : HasDerivAt p (dp x) x := by
  have h := (hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
  convert h using 1 <;> simp [p, dp] <;> ring

theorem hasDerivAt_dp (x : ℝ) : HasDerivAt dp (-2) x := by
  have h := ((hasDerivAt_id x).const_mul 2).const_sub 1
  convert h using 1 <;> simp [dp] <;> ring

theorem hasDerivAt_B (x y : ℝ) : HasDerivAt (fun t => B t y) (Bx x y) x := by
  have h := (((hasDerivAt_p x).add_const (p y)).div_const 20).sub
    ((((hasDerivAt_p x).pow 2).add_const ((p y)^2)).div_const 5)
  have hh := h.add ((((hasDerivAt_p x).const_mul 6).mul_const (p y)).div_const 5)
  convert hh using 1 <;> simp [B, Bx] <;> ring

theorem hasDerivAt_Bx (x y : ℝ) : HasDerivAt (fun t => Bx t y) (Bxx x y) x := by
  have h := ((((hasDerivAt_p x).const_mul 2).div_const 5).const_sub ((1:ℝ)/20)).add_const (6*p y/5)
  have hh := (hasDerivAt_dp x).mul h
  convert hh using 1 <;> simp [Bx, Bxx] <;> ring

theorem B_symm (x y : ℝ) : B x y = B y x := by
  dsimp [B]
  ring

theorem hasDerivAt_B_y (x y : ℝ) : HasDerivAt (fun t => B x t) (Bx y x) y := by
  simpa only [B_symm x] using hasDerivAt_B y x

theorem negative_laplacian (x y : ℝ) : -(Bxx x y+Bxx y x) = 1 := by
  dsimp [Bxx, p, dp]
  ring

/-- Only the algebraic conclusion after both PDE comparisons have been supplied. -/
theorem comparison_conclusion {x y e R : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hR : 0 ≤ R)
    (hu : e ≤ R*B x y) (hl : -e ≤ R*B x y) : |e| ≤ 3*R/40 := by
  have hb := barrier_le hx0 hx1 hy0 hy1
  have hm := mul_le_mul_of_nonneg_left hb hR
  rw [abs_le]
  constructor <;> nlinarith

#check barrier_nonneg
#check barrier_le
#check hasDerivAt_B
#check hasDerivAt_Bx
#check hasDerivAt_B_y
#check negative_laplacian
#check comparison_conclusion
#print axioms barrier_nonneg
#print axioms barrier_le
#print axioms hasDerivAt_B
#print axioms hasDerivAt_Bx
#print axioms hasDerivAt_B_y
#print axioms negative_laplacian
#print axioms comparison_conclusion
end PoissonPilot
