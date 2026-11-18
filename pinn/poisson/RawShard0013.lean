import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell418 : Cell := gridCell 64 4 6
theorem check418 : Cell.secondCheck normalizedResidual cell418 residualNumerator = true := by
  decide +kernel
theorem bound418 {x y : ℝ} (h : cell418.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell418 residualNumerator check418 h
def cell417 : Cell := gridCell 64 4 7
theorem check417 : Cell.secondCheck normalizedResidual cell417 residualNumerator = true := by
  decide +kernel
theorem bound417 {x y : ℝ} (h : cell417.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell417 residualNumerator check417 h
def cell416 : Cell := gridCell 64 5 6
theorem check416 : Cell.secondCheck normalizedResidual cell416 residualNumerator = true := by
  decide +kernel
theorem bound416 {x y : ℝ} (h : cell416.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell416 residualNumerator check416 h
def cell415 : Cell := gridCell 64 5 7
theorem check415 : Cell.secondCheck normalizedResidual cell415 residualNumerator = true := by
  decide +kernel
theorem bound415 {x y : ℝ} (h : cell415.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell415 residualNumerator check415 h
def RawShard0013Cells : List Cell := [cell418, cell417, cell416, cell415]
theorem RawShard0013Valid : ValidCells RawShard0013Cells := by
  intro c hc x y h
  simp only [RawShard0013Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h418 | h417 | h416 | h415
  · subst c
    exact bound418 h
  · subst c
    exact bound417 h
  · subst c
    exact bound416 h
  · subst c
    exact bound415 h
#print axioms RawShard0013Valid
end PinnCertFarm
