import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1293 : Cell := gridCell 64 14 14
theorem check1293 : Cell.secondCheck normalizedResidual cell1293 residualNumerator = true := by
  decide +kernel
theorem bound1293 {x y : ℝ} (h : cell1293.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1293 residualNumerator check1293 h
def cell1292 : Cell := gridCell 64 14 15
theorem check1292 : Cell.secondCheck normalizedResidual cell1292 residualNumerator = true := by
  decide +kernel
theorem bound1292 {x y : ℝ} (h : cell1292.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1292 residualNumerator check1292 h
def cell1291 : Cell := gridCell 64 15 14
theorem check1291 : Cell.secondCheck normalizedResidual cell1291 residualNumerator = true := by
  decide +kernel
theorem bound1291 {x y : ℝ} (h : cell1291.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1291 residualNumerator check1291 h
def cell1290 : Cell := gridCell 64 15 15
theorem check1290 : Cell.secondCheck normalizedResidual cell1290 residualNumerator = true := by
  decide +kernel
theorem bound1290 {x y : ℝ} (h : cell1290.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1290 residualNumerator check1290 h
def RawShard0063Cells : List Cell := [cell1293, cell1292, cell1291, cell1290]
theorem RawShard0063Valid : ValidCells RawShard0063Cells := by
  intro c hc x y h
  simp only [RawShard0063Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1293 | h1292 | h1291 | h1290
  · subst c
    exact bound1293 h
  · subst c
    exact bound1292 h
  · subst c
    exact bound1291 h
  · subst c
    exact bound1290 h
#print axioms RawShard0063Valid
end PinnCertFarm
