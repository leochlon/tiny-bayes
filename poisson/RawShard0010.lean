import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell398 : Cell := gridCell 64 6 0
theorem check398 : Cell.secondCheck normalizedResidual cell398 residualNumerator = true := by
  decide +kernel
theorem bound398 {x y : ℝ} (h : cell398.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell398 residualNumerator check398 h
def cell397 : Cell := gridCell 64 6 1
theorem check397 : Cell.secondCheck normalizedResidual cell397 residualNumerator = true := by
  decide +kernel
theorem bound397 {x y : ℝ} (h : cell397.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell397 residualNumerator check397 h
def cell396 : Cell := gridCell 64 7 0
theorem check396 : Cell.secondCheck normalizedResidual cell396 residualNumerator = true := by
  decide +kernel
theorem bound396 {x y : ℝ} (h : cell396.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell396 residualNumerator check396 h
def cell395 : Cell := gridCell 64 7 1
theorem check395 : Cell.secondCheck normalizedResidual cell395 residualNumerator = true := by
  decide +kernel
theorem bound395 {x y : ℝ} (h : cell395.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell395 residualNumerator check395 h
def RawShard0010Cells : List Cell := [cell398, cell397, cell396, cell395]
theorem RawShard0010Valid : ValidCells RawShard0010Cells := by
  intro c hc x y h
  simp only [RawShard0010Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h398 | h397 | h396 | h395
  · subst c
    exact bound398 h
  · subst c
    exact bound397 h
  · subst c
    exact bound396 h
  · subst c
    exact bound395 h
#print axioms RawShard0010Valid
end PinnCertFarm
