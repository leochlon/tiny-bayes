import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell19 : Cell := gridCell 64 2 6
theorem check19 : Cell.secondCheck normalizedResidual cell19 residualNumerator = true := by
  decide +kernel
theorem bound19 {x y : ℝ} (h : cell19.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell19 residualNumerator check19 h
def cell18 : Cell := gridCell 64 2 7
theorem check18 : Cell.secondCheck normalizedResidual cell18 residualNumerator = true := by
  decide +kernel
theorem bound18 {x y : ℝ} (h : cell18.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell18 residualNumerator check18 h
def cell17 : Cell := gridCell 64 3 6
theorem check17 : Cell.secondCheck normalizedResidual cell17 residualNumerator = true := by
  decide +kernel
theorem bound17 {x y : ℝ} (h : cell17.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell17 residualNumerator check17 h
def cell16 : Cell := gridCell 64 3 7
theorem check16 : Cell.secondCheck normalizedResidual cell16 residualNumerator = true := by
  decide +kernel
theorem bound16 {x y : ℝ} (h : cell16.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell16 residualNumerator check16 h
def RawShard0007Cells : List Cell := [cell19, cell18, cell17, cell16]
theorem RawShard0007Valid : ValidCells RawShard0007Cells := by
  intro c hc x y h
  simp only [RawShard0007Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h19 | h18 | h17 | h16
  · subst c
    exact bound19 h
  · subst c
    exact bound18 h
  · subst c
    exact bound17 h
  · subst c
    exact bound16 h
#print axioms RawShard0007Valid
end PinnCertFarm
