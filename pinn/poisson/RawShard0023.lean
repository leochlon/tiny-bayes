import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell51 : Cell := gridCell 64 2 14
theorem check51 : Cell.secondCheck normalizedResidual cell51 residualNumerator = true := by
  decide +kernel
theorem bound51 {x y : ℝ} (h : cell51.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell51 residualNumerator check51 h
def cell50 : Cell := gridCell 64 2 15
theorem check50 : Cell.secondCheck normalizedResidual cell50 residualNumerator = true := by
  decide +kernel
theorem bound50 {x y : ℝ} (h : cell50.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell50 residualNumerator check50 h
def cell49 : Cell := gridCell 64 3 14
theorem check49 : Cell.secondCheck normalizedResidual cell49 residualNumerator = true := by
  decide +kernel
theorem bound49 {x y : ℝ} (h : cell49.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell49 residualNumerator check49 h
def cell48 : Cell := gridCell 64 3 15
theorem check48 : Cell.secondCheck normalizedResidual cell48 residualNumerator = true := by
  decide +kernel
theorem bound48 {x y : ℝ} (h : cell48.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell48 residualNumerator check48 h
def RawShard0023Cells : List Cell := [cell51, cell50, cell49, cell48]
theorem RawShard0023Valid : ValidCells RawShard0023Cells := by
  intro c hc x y h
  simp only [RawShard0023Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h51 | h50 | h49 | h48
  · subst c
    exact bound51 h
  · subst c
    exact bound50 h
  · subst c
    exact bound49 h
  · subst c
    exact bound48 h
#print axioms RawShard0023Valid
end PinnCertFarm
