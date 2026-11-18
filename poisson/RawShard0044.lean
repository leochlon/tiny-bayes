import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1273 : Cell := gridCell 64 12 4
theorem check1273 : Cell.secondCheck normalizedResidual cell1273 residualNumerator = true := by
  decide +kernel
theorem bound1273 {x y : ℝ} (h : cell1273.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1273 residualNumerator check1273 h
def cell1272 : Cell := gridCell 64 12 5
theorem check1272 : Cell.secondCheck normalizedResidual cell1272 residualNumerator = true := by
  decide +kernel
theorem bound1272 {x y : ℝ} (h : cell1272.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1272 residualNumerator check1272 h
def cell1271 : Cell := gridCell 64 13 4
theorem check1271 : Cell.secondCheck normalizedResidual cell1271 residualNumerator = true := by
  decide +kernel
theorem bound1271 {x y : ℝ} (h : cell1271.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1271 residualNumerator check1271 h
def cell1270 : Cell := gridCell 64 13 5
theorem check1270 : Cell.secondCheck normalizedResidual cell1270 residualNumerator = true := by
  decide +kernel
theorem bound1270 {x y : ℝ} (h : cell1270.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1270 residualNumerator check1270 h
def RawShard0044Cells : List Cell := [cell1273, cell1272, cell1271, cell1270]
theorem RawShard0044Valid : ValidCells RawShard0044Cells := by
  intro c hc x y h
  simp only [RawShard0044Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1273 | h1272 | h1271 | h1270
  · subst c
    exact bound1273 h
  · subst c
    exact bound1272 h
  · subst c
    exact bound1271 h
  · subst c
    exact bound1270 h
#print axioms RawShard0044Valid
end PinnCertFarm
