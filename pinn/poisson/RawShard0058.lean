import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1281 : Cell := gridCell 64 14 8
theorem check1281 : Cell.secondCheck normalizedResidual cell1281 residualNumerator = true := by
  decide +kernel
theorem bound1281 {x y : ℝ} (h : cell1281.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1281 residualNumerator check1281 h
def cell1280 : Cell := gridCell 64 14 9
theorem check1280 : Cell.secondCheck normalizedResidual cell1280 residualNumerator = true := by
  decide +kernel
theorem bound1280 {x y : ℝ} (h : cell1280.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1280 residualNumerator check1280 h
def cell1279 : Cell := gridCell 64 15 8
theorem check1279 : Cell.secondCheck normalizedResidual cell1279 residualNumerator = true := by
  decide +kernel
theorem bound1279 {x y : ℝ} (h : cell1279.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1279 residualNumerator check1279 h
def cell1278 : Cell := gridCell 64 15 9
theorem check1278 : Cell.secondCheck normalizedResidual cell1278 residualNumerator = true := by
  decide +kernel
theorem bound1278 {x y : ℝ} (h : cell1278.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1278 residualNumerator check1278 h
def RawShard0058Cells : List Cell := [cell1281, cell1280, cell1279, cell1278]
theorem RawShard0058Valid : ValidCells RawShard0058Cells := by
  intro c hc x y h
  simp only [RawShard0058Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1281 | h1280 | h1279 | h1278
  · subst c
    exact bound1281 h
  · subst c
    exact bound1280 h
  · subst c
    exact bound1279 h
  · subst c
    exact bound1278 h
#print axioms RawShard0058Valid
end PinnCertFarm
