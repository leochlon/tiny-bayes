import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1301 : Cell := gridCell 64 12 14
theorem check1301 : Cell.secondCheck normalizedResidual cell1301 residualNumerator = true := by
  decide +kernel
theorem bound1301 {x y : ℝ} (h : cell1301.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1301 residualNumerator check1301 h
def cell1300 : Cell := gridCell 64 12 15
theorem check1300 : Cell.secondCheck normalizedResidual cell1300 residualNumerator = true := by
  decide +kernel
theorem bound1300 {x y : ℝ} (h : cell1300.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1300 residualNumerator check1300 h
def cell1299 : Cell := gridCell 64 13 14
theorem check1299 : Cell.secondCheck normalizedResidual cell1299 residualNumerator = true := by
  decide +kernel
theorem bound1299 {x y : ℝ} (h : cell1299.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1299 residualNumerator check1299 h
def cell1298 : Cell := gridCell 64 13 15
theorem check1298 : Cell.secondCheck normalizedResidual cell1298 residualNumerator = true := by
  decide +kernel
theorem bound1298 {x y : ℝ} (h : cell1298.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1298 residualNumerator check1298 h
def RawShard0061Cells : List Cell := [cell1301, cell1300, cell1299, cell1298]
theorem RawShard0061Valid : ValidCells RawShard0061Cells := by
  intro c hc x y h
  simp only [RawShard0061Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1301 | h1300 | h1299 | h1298
  · subst c
    exact bound1301 h
  · subst c
    exact bound1300 h
  · subst c
    exact bound1299 h
  · subst c
    exact bound1298 h
#print axioms RawShard0061Valid
end PinnCertFarm
