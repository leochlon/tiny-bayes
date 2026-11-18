import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Bounds
noncomputable section
open Finset

def basis8 (i : Fin 9) (x : ℝ) : ℝ :=
  (Nat.choose 8 i : ℝ) * x ^ (i : ℕ) * (1-x) ^ (8-(i : ℕ))
def bern8 (c : Fin 9 → ℝ) (x : ℝ) : ℝ := ∑ i, c i * basis8 i x

lemma basis8_nonneg (i : Fin 9) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis8 i x := by
  unfold basis8
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

lemma basis8_sum (x : ℝ) : (∑ i : Fin 9, basis8 i x) = 1 := by
  norm_num [basis8, Fin.sum_univ_succ, Nat.choose]
  ring

lemma bern8_le (c : Fin 9 → ℝ) (x A : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : ∀ i, c i ≤ A) : bern8 c x ≤ A := by
  calc
    bern8 c x ≤ ∑ i, A * basis8 i x :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) (basis8_nonneg i hx hx1))
    _ = A := by rw [← Finset.mul_sum, basis8_sum, mul_one]

lemma le_bern8 (c : Fin 9 → ℝ) (x A : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : ∀ i, A ≤ c i) : A ≤ bern8 c x := by
  calc
    A = ∑ i, A * basis8 i x := by rw [← Finset.mul_sum, basis8_sum, mul_one]
    _ ≤ bern8 c x :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) (basis8_nonneg i hx hx1))

def bern88 (c : Fin 9 → Fin 9 → ℝ) (x y : ℝ) : ℝ := bern8 (fun i => bern8 (c i) y) x

lemma bern88_abs_le (c : Fin 9 → Fin 9 → ℝ) (x y A : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i j, -A ≤ c i j ∧ c i j ≤ A) : |bern88 c x y| ≤ A := by
  apply abs_le.mpr
  constructor
  · exact le_bern8 _ _ _ hx hx1 (fun i => le_bern8 _ _ _ hy hy1 (fun j => (hc i j).1))
  · exact bern8_le _ _ _ hx hx1 (fun i => bern8_le _ _ _ hy hy1 (fun j => (hc i j).2))

#print axioms bern88_abs_le
end
end Bounds
