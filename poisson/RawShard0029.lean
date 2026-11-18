import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell450 : Cell := gridCell 64 4 14
theorem check450 : Cell.secondCheck normalizedResidual cell450 residualNumerator = true := by
  decide +kernel
theorem bound450 {x y : ℝ} (h : cell450.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell450 residualNumerator check450 h
def cell449 : Cell := gridCell 64 4 15
theorem check449 : Cell.secondCheck normalizedResidual cell449 residualNumerator = true := by
  decide +kernel
theorem bound449 {x y : ℝ} (h : cell449.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell449 residualNumerator check449 h
def cell448 : Cell := gridCell 64 5 14
theorem check448 : Cell.secondCheck normalizedResidual cell448 residualNumerator = true := by
  decide +kernel
theorem bound448 {x y : ℝ} (h : cell448.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell448 residualNumerator check448 h
def cell447 : Cell := gridCell 64 5 15
theorem check447 : Cell.secondCheck normalizedResidual cell447 residualNumerator = true := by
  decide +kernel
theorem bound447 {x y : ℝ} (h : cell447.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell447 residualNumerator check447 h
def RawShard0029Cells : List Cell := [cell450, cell449, cell448, cell447]
theorem RawShard0029Valid : ValidCells RawShard0029Cells := by
  intro c hc x y h
  simp only [RawShard0029Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h450 | h449 | h448 | h447
  · subst c
    exact bound450 h
  · subst c
    exact bound449 h
  · subst c
    exact bound448 h
  · subst c
    exact bound447 h
#print axioms RawShard0029Valid
end PinnCertFarm
