import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell843 : Cell := gridCell 64 8 4
theorem check843 : Cell.secondCheck normalizedResidual cell843 residualNumerator = true := by
  decide +kernel
theorem bound843 {x y : ℝ} (h : cell843.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell843 residualNumerator check843 h
def cell842 : Cell := gridCell 64 8 5
theorem check842 : Cell.secondCheck normalizedResidual cell842 residualNumerator = true := by
  decide +kernel
theorem bound842 {x y : ℝ} (h : cell842.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell842 residualNumerator check842 h
def cell841 : Cell := gridCell 64 9 4
theorem check841 : Cell.secondCheck normalizedResidual cell841 residualNumerator = true := by
  decide +kernel
theorem bound841 {x y : ℝ} (h : cell841.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell841 residualNumerator check841 h
def cell840 : Cell := gridCell 64 9 5
theorem check840 : Cell.secondCheck normalizedResidual cell840 residualNumerator = true := by
  decide +kernel
theorem bound840 {x y : ℝ} (h : cell840.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell840 residualNumerator check840 h
def RawShard0036Cells : List Cell := [cell843, cell842, cell841, cell840]
theorem RawShard0036Valid : ValidCells RawShard0036Cells := by
  intro c hc x y h
  simp only [RawShard0036Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h843 | h842 | h841 | h840
  · subst c
    exact bound843 h
  · subst c
    exact bound842 h
  · subst c
    exact bound841 h
  · subst c
    exact bound840 h
#print axioms RawShard0036Valid
end PinnCertFarm
