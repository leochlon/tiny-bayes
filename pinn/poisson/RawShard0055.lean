import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell863 : Cell := gridCell 64 10 14
theorem check863 : Cell.secondCheck normalizedResidual cell863 residualNumerator = true := by
  decide +kernel
theorem bound863 {x y : ℝ} (h : cell863.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell863 residualNumerator check863 h
def cell862 : Cell := gridCell 64 10 15
theorem check862 : Cell.secondCheck normalizedResidual cell862 residualNumerator = true := by
  decide +kernel
theorem bound862 {x y : ℝ} (h : cell862.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell862 residualNumerator check862 h
def cell861 : Cell := gridCell 64 11 14
theorem check861 : Cell.secondCheck normalizedResidual cell861 residualNumerator = true := by
  decide +kernel
theorem bound861 {x y : ℝ} (h : cell861.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell861 residualNumerator check861 h
def cell860 : Cell := gridCell 64 11 15
theorem check860 : Cell.secondCheck normalizedResidual cell860 residualNumerator = true := by
  decide +kernel
theorem bound860 {x y : ℝ} (h : cell860.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell860 residualNumerator check860 h
def RawShard0055Cells : List Cell := [cell863, cell862, cell861, cell860]
theorem RawShard0055Valid : ValidCells RawShard0055Cells := by
  intro c hc x y h
  simp only [RawShard0055Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h863 | h862 | h861 | h860
  · subst c
    exact bound863 h
  · subst c
    exact bound862 h
  · subst c
    exact bound861 h
  · subst c
    exact bound860 h
#print axioms RawShard0055Valid
end PinnCertFarm
