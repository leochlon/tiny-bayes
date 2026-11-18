import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell414 : Cell := gridCell 64 6 4
theorem check414 : Cell.secondCheck normalizedResidual cell414 residualNumerator = true := by
  decide +kernel
theorem bound414 {x y : ℝ} (h : cell414.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell414 residualNumerator check414 h
def cell413 : Cell := gridCell 64 6 5
theorem check413 : Cell.secondCheck normalizedResidual cell413 residualNumerator = true := by
  decide +kernel
theorem bound413 {x y : ℝ} (h : cell413.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell413 residualNumerator check413 h
def cell412 : Cell := gridCell 64 7 4
theorem check412 : Cell.secondCheck normalizedResidual cell412 residualNumerator = true := by
  decide +kernel
theorem bound412 {x y : ℝ} (h : cell412.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell412 residualNumerator check412 h
def cell411 : Cell := gridCell 64 7 5
theorem check411 : Cell.secondCheck normalizedResidual cell411 residualNumerator = true := by
  decide +kernel
theorem bound411 {x y : ℝ} (h : cell411.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell411 residualNumerator check411 h
def RawShard0014Cells : List Cell := [cell414, cell413, cell412, cell411]
theorem RawShard0014Valid : ValidCells RawShard0014Cells := by
  intro c hc x y h
  simp only [RawShard0014Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h414 | h413 | h412 | h411
  · subst c
    exact bound414 h
  · subst c
    exact bound413 h
  · subst c
    exact bound412 h
  · subst c
    exact bound411 h
#print axioms RawShard0014Valid
end PinnCertFarm
