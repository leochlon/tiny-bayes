import Frozen

/-! FROZEN CONDITIONAL checkpoint theorem. The three uniform/point numerical
premises below are NOT discharged. No completed neural certificate is claimed. -/
namespace PoissonR3
open Set PoissonPilot
noncomputable section

def certA : ℝ := 236872676565396/18446744073709551616
def certR : ℝ := 4831208875216605/18446744073709551616
def certL : ℝ := 238261335216327/18446744073709551616
def certU : ℝ := certA+3*certR/40
def witness : ℝ × ℝ := (100/256,97/256)

theorem candidate_arithmetic : certU < (1:ℝ)/30000 ∧ (1:ℝ)/80000 ≤ certL ∧
    certU < (63:ℝ)/25*certL := by
  norm_num [certA,certR,certL,certU]

theorem frozen_upper_conditional
    (hC : ∀ z ∈ Q, |C z.1 z.2| ≤ certA)
    (hres : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      |(-Lap (fun x y => N x y-C x y) x y)-forcing x y| ≤ certR)
    (u : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q) (hdu : CoordTwoOn u)
    (hbu : ∀ z ∈ Q, Edge z → u z.1 z.2=0)
    (hpu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=forcing x y) :
    ∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ certU := by
  exact corrected_poisson N u C forcing certA certR (by norm_num [certR])
    N_smooth.continuous.continuousOn hcu C_smooth.continuous.continuousOn
    (coord_of_smooth N N_smooth) hdu (coord_of_smooth C C_smooth)
    (fun z hz he => ⟨N_boundary z he,hbu z hz he,C_boundary z he⟩) hpu hC hres

theorem frozen_bracket_conditional
    (hC : ∀ z ∈ Q, |C z.1 z.2| ≤ certA)
    (hres : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      |(-Lap (fun x y => N x y-C x y) x y)-forcing x y| ≤ certR)
    (hpoint : N witness.1 witness.2-U witness.1 witness.2 ≤ -certL)
    (u : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q) (hdu : CoordTwoOn u)
    (hbu : ∀ z ∈ Q, Edge z → u z.1 z.2=0)
    (hpu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=forcing x y) :
    (∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ certU) ∧
      certL ≤ |N witness.1 witness.2-u witness.1 witness.2| := by
  refine ⟨frozen_upper_conditional hC hres u hcu hdu hbu hpu, ?_⟩
  have hu := poisson_unique u U forcing hcu U_smooth.continuous.continuousOn
    hdu (coord_of_smooth U U_smooth)
    (fun z hz he => by rw [hbu z hz he,U_boundary z he]) hpu
    (fun x y _ _ => manufactured_pde x y)
  have hw : witness ∈ Q := by norm_num [witness,Q]
  rw [hu witness hw]
  have h := neg_le_abs (N witness.1 witness.2-U witness.1 witness.2)
  linarith

/-- Nonvacuity: the manufactured reference satisfies all classical solution assumptions. -/
theorem reference_is_solution :
    ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) Q ∧ CoordTwoOn U ∧
    (∀ z ∈ Q, Edge z → U z.1 z.2=0) ∧
    (∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap U x y=forcing x y) := by
  exact ⟨U_smooth.continuous.continuousOn,coord_of_smooth U U_smooth,
    fun z _ he => U_boundary z he, fun x y _ _ => manufactured_pde x y⟩

#check candidate_arithmetic
#check frozen_upper_conditional
#check frozen_bracket_conditional
#check reference_is_solution
#print axioms candidate_arithmetic
#print axioms frozen_upper_conditional
#print axioms frozen_bracket_conditional
#print axioms reference_is_solution
end
end PoissonR3
