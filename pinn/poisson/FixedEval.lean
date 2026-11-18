import FixedSound
namespace BoundsInterval

lemma eval_tanh (n l u : ℤ) (heval : tanhI (cst n) = ⟨l,u,true⟩) :
    (l : ℝ) ≤ Real.tanh ((n : ℝ)/S)*S ∧ Real.tanh ((n : ℝ)/S)*S ≤ u := by
  have hx : memAt S ((n : ℝ)/S) (cst n) := by
    apply memAt_cst
    field_simp [S]
  have h := memAt_tanh hx
  rw [heval] at h
  exact h rfl

lemma eval_exp (n l u : ℤ) (heval : expI (cst n) = ⟨l,u,true⟩) :
    (l : ℝ) ≤ Real.exp ((n : ℝ)/S)*S ∧ Real.exp ((n : ℝ)/S)*S ≤ u := by
  have hx : memAt S ((n : ℝ)/S) (cst n) := by
    apply memAt_cst
    field_simp [S]
  have h := memAt_exp hx
  rw [heval] at h
  exact h rfl

#print axioms eval_tanh
#print axioms eval_exp
end BoundsInterval
