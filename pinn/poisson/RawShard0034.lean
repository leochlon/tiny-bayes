import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell819 : Cell := gridCell 64 10 0
theorem check819 : Cell.secondCheck normalizedResidual cell819 residualNumerator = true := by
  decide +kernel
theorem bound819 {x y : ℝ} (h : cell819.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell819 residualNumerator check819 h
def cell818 : Cell := gridCell 64 10 1
theorem check818 : Cell.secondCheck normalizedResidual cell818 residualNumerator = true := by
  decide +kernel
theorem bound818 {x y : ℝ} (h : cell818.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell818 residualNumerator check818 h
def cell817 : Cell := gridCell 64 11 0
theorem check817 : Cell.secondCheck normalizedResidual cell817 residualNumerator = true := by
  decide +kernel
theorem bound817 {x y : ℝ} (h : cell817.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell817 residualNumerator check817 h
def cell816 : Cell := gridCell 64 11 1
theorem check816 : Cell.secondCheck normalizedResidual cell816 residualNumerator = true := by
  decide +kernel
theorem bound816 {x y : ℝ} (h : cell816.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell816 residualNumerator check816 h
def RawShard0034Cells : List Cell := [cell819, cell818, cell817, cell816]
theorem RawShard0034Valid : ValidCells RawShard0034Cells := by
  intro c hc x y h
  simp only [RawShard0034Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h819 | h818 | h817 | h816
  · subst c
    exact bound819 h
  · subst c
    exact bound818 h
  · subst c
    exact bound817 h
  · subst c
    exact bound816 h
#print axioms RawShard0034Valid
end PinnCertFarm
