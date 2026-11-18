import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell7 : Cell := gridCell 64 2 0
theorem check7 : Cell.secondCheck normalizedResidual cell7 residualNumerator = true := by
  decide +kernel
theorem bound7 {x y : ℝ} (h : cell7.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell7 residualNumerator check7 h
def cell6 : Cell := gridCell 64 2 1
theorem check6 : Cell.secondCheck normalizedResidual cell6 residualNumerator = true := by
  decide +kernel
theorem bound6 {x y : ℝ} (h : cell6.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell6 residualNumerator check6 h
def cell5 : Cell := gridCell 64 3 0
theorem check5 : Cell.secondCheck normalizedResidual cell5 residualNumerator = true := by
  decide +kernel
theorem bound5 {x y : ℝ} (h : cell5.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell5 residualNumerator check5 h
def cell4 : Cell := gridCell 64 3 1
theorem check4 : Cell.secondCheck normalizedResidual cell4 residualNumerator = true := by
  decide +kernel
theorem bound4 {x y : ℝ} (h : cell4.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell4 residualNumerator check4 h
def RawShard0002Cells : List Cell := [cell7, cell6, cell5, cell4]
theorem RawShard0002Valid : ValidCells RawShard0002Cells := by
  intro c hc x y h
  simp only [RawShard0002Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h7 | h6 | h5 | h4
  · subst c
    exact bound7 h
  · subst c
    exact bound6 h
  · subst c
    exact bound5 h
  · subst c
    exact bound4 h
#print axioms RawShard0002Valid
end PinnCertFarm
