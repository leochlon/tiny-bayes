import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell847 : Cell := gridCell 64 10 10
theorem check847 : Cell.secondCheck normalizedResidual cell847 residualNumerator = true := by
  decide +kernel
theorem bound847 {x y : ℝ} (h : cell847.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell847 residualNumerator check847 h
def cell846 : Cell := gridCell 64 10 11
theorem check846 : Cell.secondCheck normalizedResidual cell846 residualNumerator = true := by
  decide +kernel
theorem bound846 {x y : ℝ} (h : cell846.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell846 residualNumerator check846 h
def cell845 : Cell := gridCell 64 11 10
theorem check845 : Cell.secondCheck normalizedResidual cell845 residualNumerator = true := by
  decide +kernel
theorem bound845 {x y : ℝ} (h : cell845.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell845 residualNumerator check845 h
def cell844 : Cell := gridCell 64 11 11
theorem check844 : Cell.secondCheck normalizedResidual cell844 residualNumerator = true := by
  decide +kernel
theorem bound844 {x y : ℝ} (h : cell844.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell844 residualNumerator check844 h
def RawShard0051Cells : List Cell := [cell847, cell846, cell845, cell844]
theorem RawShard0051Valid : ValidCells RawShard0051Cells := by
  intro c hc x y h
  simp only [RawShard0051Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h847 | h846 | h845 | h844
  · subst c
    exact bound847 h
  · subst c
    exact bound846 h
  · subst c
    exact bound845 h
  · subst c
    exact bound844 h
#print axioms RawShard0051Valid
end PinnCertFarm
