import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell406 : Cell := gridCell 64 4 0
theorem check406 : Cell.secondCheck normalizedResidual cell406 residualNumerator = true := by
  decide +kernel
theorem bound406 {x y : ℝ} (h : cell406.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell406 residualNumerator check406 h
def cell405 : Cell := gridCell 64 4 1
theorem check405 : Cell.secondCheck normalizedResidual cell405 residualNumerator = true := by
  decide +kernel
theorem bound405 {x y : ℝ} (h : cell405.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell405 residualNumerator check405 h
def cell404 : Cell := gridCell 64 5 0
theorem check404 : Cell.secondCheck normalizedResidual cell404 residualNumerator = true := by
  decide +kernel
theorem bound404 {x y : ℝ} (h : cell404.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell404 residualNumerator check404 h
def cell403 : Cell := gridCell 64 5 1
theorem check403 : Cell.secondCheck normalizedResidual cell403 residualNumerator = true := by
  decide +kernel
theorem bound403 {x y : ℝ} (h : cell403.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell403 residualNumerator check403 h
def RawShard0008Cells : List Cell := [cell406, cell405, cell404, cell403]
theorem RawShard0008Valid : ValidCells RawShard0008Cells := by
  intro c hc x y h
  simp only [RawShard0008Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h406 | h405 | h404 | h403
  · subst c
    exact bound406 h
  · subst c
    exact bound405 h
  · subst c
    exact bound404 h
  · subst c
    exact bound403 h
#print axioms RawShard0008Valid
end PinnCertFarm
