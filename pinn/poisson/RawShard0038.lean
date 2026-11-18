import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell835 : Cell := gridCell 64 10 4
theorem check835 : Cell.secondCheck normalizedResidual cell835 residualNumerator = true := by
  decide +kernel
theorem bound835 {x y : ℝ} (h : cell835.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell835 residualNumerator check835 h
def cell834 : Cell := gridCell 64 10 5
theorem check834 : Cell.secondCheck normalizedResidual cell834 residualNumerator = true := by
  decide +kernel
theorem bound834 {x y : ℝ} (h : cell834.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell834 residualNumerator check834 h
def cell833 : Cell := gridCell 64 11 4
theorem check833 : Cell.secondCheck normalizedResidual cell833 residualNumerator = true := by
  decide +kernel
theorem bound833 {x y : ℝ} (h : cell833.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell833 residualNumerator check833 h
def cell832 : Cell := gridCell 64 11 5
theorem check832 : Cell.secondCheck normalizedResidual cell832 residualNumerator = true := by
  decide +kernel
theorem bound832 {x y : ℝ} (h : cell832.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell832 residualNumerator check832 h
def RawShard0038Cells : List Cell := [cell835, cell834, cell833, cell832]
theorem RawShard0038Valid : ValidCells RawShard0038Cells := by
  intro c hc x y h
  simp only [RawShard0038Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h835 | h834 | h833 | h832
  · subst c
    exact bound835 h
  · subst c
    exact bound834 h
  · subst c
    exact bound833 h
  · subst c
    exact bound832 h
#print axioms RawShard0038Valid
end PinnCertFarm
