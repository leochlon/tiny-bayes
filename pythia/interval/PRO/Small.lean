import Mathlib
import PRO.Claim
import PRO.Sound

/-! Order averages on the six bags with at most two observations, as explicit expressions. -/

namespace PRO

theorem avg_list (q : List Bool → ℝ) (n k : ℕ) :
    avg q n k = (1 / (n.choose k : ℝ)) * ((orderings n k).map q).sum := by
  unfold avg
  rw [bag_sum]

theorem avg_0_0 (q : List Bool → ℝ) : avg q 0 0 = q [] := by
  rw [avg_list, show orderings 0 0 = [[]] from by decide, show Nat.choose 0 0 = 1 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem avg_1_0 (q : List Bool → ℝ) : avg q 1 0 = q [false] := by
  rw [avg_list, show orderings 1 0 = [[false]] from by decide, show Nat.choose 1 0 = 1 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem avg_1_1 (q : List Bool → ℝ) : avg q 1 1 = q [true] := by
  rw [avg_list, show orderings 1 1 = [[true]] from by decide, show Nat.choose 1 1 = 1 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem avg_2_0 (q : List Bool → ℝ) : avg q 2 0 = q [false, false] := by
  rw [avg_list, show orderings 2 0 = [[false, false]] from by decide,
    show Nat.choose 2 0 = 1 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem avg_2_1 (q : List Bool → ℝ) : avg q 2 1 = (q [false, true] + q [true, false]) / 2 := by
  rw [avg_list, show orderings 2 1 = [[false, true], [true, false]] from by decide,
    show Nat.choose 2 1 = 2 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem avg_2_2 (q : List Bool → ℝ) : avg q 2 2 = q [true, true] := by
  rw [avg_list, show orderings 2 2 = [[true, true]] from by decide,
    show Nat.choose 2 2 = 1 from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

end PRO
