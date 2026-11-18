import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell855 : Cell := gridCell 64 8 10
theorem check855 : Cell.secondCheck normalizedResidual cell855 residualNumerator = true := by
  decide +kernel
theorem bound855 {x y : ℝ} (h : cell855.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell855 residualNumerator check855 h
def cell854 : Cell := gridCell 64 8 11
theorem check854 : Cell.secondCheck normalizedResidual cell854 residualNumerator = true := by
  decide +kernel
theorem bound854 {x y : ℝ} (h : cell854.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell854 residualNumerator check854 h
def cell853 : Cell := gridCell 64 9 10
theorem check853 : Cell.secondCheck normalizedResidual cell853 residualNumerator = true := by
  decide +kernel
theorem bound853 {x y : ℝ} (h : cell853.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell853 residualNumerator check853 h
def cell852 : Cell := gridCell 64 9 11
theorem check852 : Cell.secondCheck normalizedResidual cell852 residualNumerator = true := by
  decide +kernel
theorem bound852 {x y : ℝ} (h : cell852.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell852 residualNumerator check852 h
def RawShard0049Cells : List Cell := [cell855, cell854, cell853, cell852]
theorem RawShard0049Valid : ValidCells RawShard0049Cells := by
  intro c hc x y h
  simp only [RawShard0049Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h855 | h854 | h853 | h852
  · subst c
    exact bound855 h
  · subst c
    exact bound854 h
  · subst c
    exact bound853 h
  · subst c
    exact bound852 h
#print axioms RawShard0049Valid
end PinnCertFarm
