import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1249 : Cell := gridCell 64 14 0
theorem check1249 : Cell.secondCheck normalizedResidual cell1249 residualNumerator = true := by
  decide +kernel
theorem bound1249 {x y : ℝ} (h : cell1249.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1249 residualNumerator check1249 h
def cell1248 : Cell := gridCell 64 14 1
theorem check1248 : Cell.secondCheck normalizedResidual cell1248 residualNumerator = true := by
  decide +kernel
theorem bound1248 {x y : ℝ} (h : cell1248.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1248 residualNumerator check1248 h
def cell1247 : Cell := gridCell 64 15 0
theorem check1247 : Cell.secondCheck normalizedResidual cell1247 residualNumerator = true := by
  decide +kernel
theorem bound1247 {x y : ℝ} (h : cell1247.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1247 residualNumerator check1247 h
def cell1246 : Cell := gridCell 64 15 1
theorem check1246 : Cell.secondCheck normalizedResidual cell1246 residualNumerator = true := by
  decide +kernel
theorem bound1246 {x y : ℝ} (h : cell1246.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1246 residualNumerator check1246 h
def RawShard0042Cells : List Cell := [cell1249, cell1248, cell1247, cell1246]
theorem RawShard0042Valid : ValidCells RawShard0042Cells := by
  intro c hc x y h
  simp only [RawShard0042Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1249 | h1248 | h1247 | h1246
  · subst c
    exact bound1249 h
  · subst c
    exact bound1248 h
  · subst c
    exact bound1247 h
  · subst c
    exact bound1246 h
#print axioms RawShard0042Valid
end PinnCertFarm
