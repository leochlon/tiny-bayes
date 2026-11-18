import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1277 : Cell := gridCell 64 14 10
theorem check1277 : Cell.secondCheck normalizedResidual cell1277 residualNumerator = true := by
  decide +kernel
theorem bound1277 {x y : ℝ} (h : cell1277.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1277 residualNumerator check1277 h
def cell1276 : Cell := gridCell 64 14 11
theorem check1276 : Cell.secondCheck normalizedResidual cell1276 residualNumerator = true := by
  decide +kernel
theorem bound1276 {x y : ℝ} (h : cell1276.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1276 residualNumerator check1276 h
def cell1275 : Cell := gridCell 64 15 10
theorem check1275 : Cell.secondCheck normalizedResidual cell1275 residualNumerator = true := by
  decide +kernel
theorem bound1275 {x y : ℝ} (h : cell1275.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1275 residualNumerator check1275 h
def cell1274 : Cell := gridCell 64 15 11
theorem check1274 : Cell.secondCheck normalizedResidual cell1274 residualNumerator = true := by
  decide +kernel
theorem bound1274 {x y : ℝ} (h : cell1274.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1274 residualNumerator check1274 h
def RawShard0059Cells : List Cell := [cell1277, cell1276, cell1275, cell1274]
theorem RawShard0059Valid : ValidCells RawShard0059Cells := by
  intro c hc x y h
  simp only [RawShard0059Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1277 | h1276 | h1275 | h1274
  · subst c
    exact bound1277 h
  · subst c
    exact bound1276 h
  · subst c
    exact bound1275 h
  · subst c
    exact bound1274 h
#print axioms RawShard0059Valid
end PinnCertFarm
