import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell402 : Cell := gridCell 64 4 2
theorem check402 : Cell.secondCheck normalizedResidual cell402 residualNumerator = true := by
  decide +kernel
theorem bound402 {x y : ℝ} (h : cell402.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell402 residualNumerator check402 h
def cell401 : Cell := gridCell 64 4 3
theorem check401 : Cell.secondCheck normalizedResidual cell401 residualNumerator = true := by
  decide +kernel
theorem bound401 {x y : ℝ} (h : cell401.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell401 residualNumerator check401 h
def cell400 : Cell := gridCell 64 5 2
theorem check400 : Cell.secondCheck normalizedResidual cell400 residualNumerator = true := by
  decide +kernel
theorem bound400 {x y : ℝ} (h : cell400.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell400 residualNumerator check400 h
def cell399 : Cell := gridCell 64 5 3
theorem check399 : Cell.secondCheck normalizedResidual cell399 residualNumerator = true := by
  decide +kernel
theorem bound399 {x y : ℝ} (h : cell399.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell399 residualNumerator check399 h
def RawShard0009Cells : List Cell := [cell402, cell401, cell400, cell399]
theorem RawShard0009Valid : ValidCells RawShard0009Cells := by
  intro c hc x y h
  simp only [RawShard0009Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h402 | h401 | h400 | h399
  · subst c
    exact bound402 h
  · subst c
    exact bound401 h
  · subst c
    exact bound400 h
  · subst c
    exact bound399 h
#print axioms RawShard0009Valid
end PinnCertFarm
