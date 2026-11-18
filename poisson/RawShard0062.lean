import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1297 : Cell := gridCell 64 14 12
theorem check1297 : Cell.secondCheck normalizedResidual cell1297 residualNumerator = true := by
  decide +kernel
theorem bound1297 {x y : ℝ} (h : cell1297.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1297 residualNumerator check1297 h
def cell1296 : Cell := gridCell 64 14 13
theorem check1296 : Cell.secondCheck normalizedResidual cell1296 residualNumerator = true := by
  decide +kernel
theorem bound1296 {x y : ℝ} (h : cell1296.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1296 residualNumerator check1296 h
def cell1295 : Cell := gridCell 64 15 12
theorem check1295 : Cell.secondCheck normalizedResidual cell1295 residualNumerator = true := by
  decide +kernel
theorem bound1295 {x y : ℝ} (h : cell1295.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1295 residualNumerator check1295 h
def cell1294 : Cell := gridCell 64 15 13
theorem check1294 : Cell.secondCheck normalizedResidual cell1294 residualNumerator = true := by
  decide +kernel
theorem bound1294 {x y : ℝ} (h : cell1294.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1294 residualNumerator check1294 h
def RawShard0062Cells : List Cell := [cell1297, cell1296, cell1295, cell1294]
theorem RawShard0062Valid : ValidCells RawShard0062Cells := by
  intro c hc x y h
  simp only [RawShard0062Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1297 | h1296 | h1295 | h1294
  · subst c
    exact bound1297 h
  · subst c
    exact bound1296 h
  · subst c
    exact bound1295 h
  · subst c
    exact bound1294 h
#print axioms RawShard0062Valid
end PinnCertFarm
