import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell859 : Cell := gridCell 64 8 8
theorem check859 : Cell.secondCheck normalizedResidual cell859 residualNumerator = true := by
  decide +kernel
theorem bound859 {x y : ℝ} (h : cell859.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell859 residualNumerator check859 h
def cell858 : Cell := gridCell 64 8 9
theorem check858 : Cell.secondCheck normalizedResidual cell858 residualNumerator = true := by
  decide +kernel
theorem bound858 {x y : ℝ} (h : cell858.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell858 residualNumerator check858 h
def cell857 : Cell := gridCell 64 9 8
theorem check857 : Cell.secondCheck normalizedResidual cell857 residualNumerator = true := by
  decide +kernel
theorem bound857 {x y : ℝ} (h : cell857.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell857 residualNumerator check857 h
def cell856 : Cell := gridCell 64 9 9
theorem check856 : Cell.secondCheck normalizedResidual cell856 residualNumerator = true := by
  decide +kernel
theorem bound856 {x y : ℝ} (h : cell856.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell856 residualNumerator check856 h
def RawShard0048Cells : List Cell := [cell859, cell858, cell857, cell856]
theorem RawShard0048Valid : ValidCells RawShard0048Cells := by
  intro c hc x y h
  simp only [RawShard0048Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h859 | h858 | h857 | h856
  · subst c
    exact bound859 h
  · subst c
    exact bound858 h
  · subst c
    exact bound857 h
  · subst c
    exact bound856 h
#print axioms RawShard0048Valid
end PinnCertFarm
