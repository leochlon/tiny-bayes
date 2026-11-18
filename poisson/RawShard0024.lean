import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell438 : Cell := gridCell 64 4 8
theorem check438 : Cell.secondCheck normalizedResidual cell438 residualNumerator = true := by
  decide +kernel
theorem bound438 {x y : ℝ} (h : cell438.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell438 residualNumerator check438 h
def cell437 : Cell := gridCell 64 4 9
theorem check437 : Cell.secondCheck normalizedResidual cell437 residualNumerator = true := by
  decide +kernel
theorem bound437 {x y : ℝ} (h : cell437.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell437 residualNumerator check437 h
def cell436 : Cell := gridCell 64 5 8
theorem check436 : Cell.secondCheck normalizedResidual cell436 residualNumerator = true := by
  decide +kernel
theorem bound436 {x y : ℝ} (h : cell436.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell436 residualNumerator check436 h
def cell435 : Cell := gridCell 64 5 9
theorem check435 : Cell.secondCheck normalizedResidual cell435 residualNumerator = true := by
  decide +kernel
theorem bound435 {x y : ℝ} (h : cell435.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell435 residualNumerator check435 h
def RawShard0024Cells : List Cell := [cell438, cell437, cell436, cell435]
theorem RawShard0024Valid : ValidCells RawShard0024Cells := by
  intro c hc x y h
  simp only [RawShard0024Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h438 | h437 | h436 | h435
  · subst c
    exact bound438 h
  · subst c
    exact bound437 h
  · subst c
    exact bound436 h
  · subst c
    exact bound435 h
#print axioms RawShard0024Valid
end PinnCertFarm
