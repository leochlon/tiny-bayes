import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell410 : Cell := gridCell 64 6 6
theorem check410 : Cell.secondCheck normalizedResidual cell410 residualNumerator = true := by
  decide +kernel
theorem bound410 {x y : ℝ} (h : cell410.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell410 residualNumerator check410 h
def cell409 : Cell := gridCell 64 6 7
theorem check409 : Cell.secondCheck normalizedResidual cell409 residualNumerator = true := by
  decide +kernel
theorem bound409 {x y : ℝ} (h : cell409.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell409 residualNumerator check409 h
def cell408 : Cell := gridCell 64 7 6
theorem check408 : Cell.secondCheck normalizedResidual cell408 residualNumerator = true := by
  decide +kernel
theorem bound408 {x y : ℝ} (h : cell408.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell408 residualNumerator check408 h
def cell407 : Cell := gridCell 64 7 7
theorem check407 : Cell.secondCheck normalizedResidual cell407 residualNumerator = true := by
  decide +kernel
theorem bound407 {x y : ℝ} (h : cell407.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell407 residualNumerator check407 h
def RawShard0015Cells : List Cell := [cell410, cell409, cell408, cell407]
theorem RawShard0015Valid : ValidCells RawShard0015Cells := by
  intro c hc x y h
  simp only [RawShard0015Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h410 | h409 | h408 | h407
  · subst c
    exact bound410 h
  · subst c
    exact bound409 h
  · subst c
    exact bound408 h
  · subst c
    exact bound407 h
#print axioms RawShard0015Valid
end PinnCertFarm
