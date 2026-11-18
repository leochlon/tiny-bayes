import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell871 : Cell := gridCell 64 8 14
theorem check871 : Cell.secondCheck normalizedResidual cell871 residualNumerator = true := by
  decide +kernel
theorem bound871 {x y : ℝ} (h : cell871.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell871 residualNumerator check871 h
def cell870 : Cell := gridCell 64 8 15
theorem check870 : Cell.secondCheck normalizedResidual cell870 residualNumerator = true := by
  decide +kernel
theorem bound870 {x y : ℝ} (h : cell870.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell870 residualNumerator check870 h
def cell869 : Cell := gridCell 64 9 14
theorem check869 : Cell.secondCheck normalizedResidual cell869 residualNumerator = true := by
  decide +kernel
theorem bound869 {x y : ℝ} (h : cell869.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell869 residualNumerator check869 h
def cell868 : Cell := gridCell 64 9 15
theorem check868 : Cell.secondCheck normalizedResidual cell868 residualNumerator = true := by
  decide +kernel
theorem bound868 {x y : ℝ} (h : cell868.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell868 residualNumerator check868 h
def RawShard0053Cells : List Cell := [cell871, cell870, cell869, cell868]
theorem RawShard0053Valid : ValidCells RawShard0053Cells := by
  intro c hc x y h
  simp only [RawShard0053Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h871 | h870 | h869 | h868
  · subst c
    exact bound871 h
  · subst c
    exact bound870 h
  · subst c
    exact bound869 h
  · subst c
    exact bound868 h
#print axioms RawShard0053Valid
end PinnCertFarm
