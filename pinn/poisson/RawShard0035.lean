import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell815 : Cell := gridCell 64 10 2
theorem check815 : Cell.secondCheck normalizedResidual cell815 residualNumerator = true := by
  decide +kernel
theorem bound815 {x y : ℝ} (h : cell815.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell815 residualNumerator check815 h
def cell814 : Cell := gridCell 64 10 3
theorem check814 : Cell.secondCheck normalizedResidual cell814 residualNumerator = true := by
  decide +kernel
theorem bound814 {x y : ℝ} (h : cell814.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell814 residualNumerator check814 h
def cell813 : Cell := gridCell 64 11 2
theorem check813 : Cell.secondCheck normalizedResidual cell813 residualNumerator = true := by
  decide +kernel
theorem bound813 {x y : ℝ} (h : cell813.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell813 residualNumerator check813 h
def cell812 : Cell := gridCell 64 11 3
theorem check812 : Cell.secondCheck normalizedResidual cell812 residualNumerator = true := by
  decide +kernel
theorem bound812 {x y : ℝ} (h : cell812.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell812 residualNumerator check812 h
def RawShard0035Cells : List Cell := [cell815, cell814, cell813, cell812]
theorem RawShard0035Valid : ValidCells RawShard0035Cells := by
  intro c hc x y h
  simp only [RawShard0035Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h815 | h814 | h813 | h812
  · subst c
    exact bound815 h
  · subst c
    exact bound814 h
  · subst c
    exact bound813 h
  · subst c
    exact bound812 h
#print axioms RawShard0035Valid
end PinnCertFarm
