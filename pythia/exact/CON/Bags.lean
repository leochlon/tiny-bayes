import Mathlib
import CON.Model
import CON.Invariance

/-! # Bag averages and the pure bags

`avg p n k` is the expression of `TinyBayes.bayes_in_expectation`: the uniform average of `p` over the
`C(n,k)` orderings of `k` ones and `n - k` zeros. The bags `(n, 0)` and `(n, n)` have one ordering. -/

namespace CON

noncomputable section

/-- Uniform average of `p` over the orderings of the bag `(n, k)`. -/
def avg (p : List Bool → ℝ) (n k : ℕ) : ℝ :=
  (1 / (n.choose k : ℝ)) * ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k),
    p (List.ofFn x)

end

theorem filter_zero (n : ℕ) :
    Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = 0) = {fun _ => false} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, List.count_eq_zero]
  constructor
  · intro h
    funext i
    by_contra hx
    apply h
    exact List.mem_ofFn.mpr ⟨i, by simpa using hx⟩
  · rintro rfl
    simp [List.mem_ofFn]

theorem filter_full (n : ℕ) :
    Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = n) = {fun _ => true} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have h' : (List.ofFn x).count true = (List.ofFn x).length := by rw [h, List.length_ofFn]
    rw [List.count_eq_length] at h'
    funext i
    exact (h' (x i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).symm
  · rintro rfl
    simp [List.ofFn_const]

/-- The bag `(n, 0)` has the single ordering `0^n`. -/
theorem avg_zero (p : List Bool → ℝ) (n : ℕ) : avg p n 0 = p (List.replicate n false) := by
  unfold avg
  rw [filter_zero, Finset.sum_singleton, Nat.choose_zero_right, List.ofFn_const]
  simp

/-- The bag `(n, n)` has the single ordering `1^n`. -/
theorem avg_full (p : List Bool → ℝ) (n : ℕ) : avg p n n = p (List.replicate n true) := by
  unfold avg
  rw [filter_full, Finset.sum_singleton, Nat.choose_self, List.ofFn_const]
  simp

end CON
