import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell442 : Cell := gridCell 64 6 14
theorem check442 : Cell.secondCheck normalizedResidual cell442 residualNumerator = true := by
  decide +kernel
theorem bound442 {x y : ℝ} (h : cell442.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell442 residualNumerator check442 h
def cell441 : Cell := gridCell 64 6 15
theorem check441 : Cell.secondCheck normalizedResidual cell441 residualNumerator = true := by
  decide +kernel
theorem bound441 {x y : ℝ} (h : cell441.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell441 residualNumerator check441 h
def cell440 : Cell := gridCell 64 7 14
theorem check440 : Cell.secondCheck normalizedResidual cell440 residualNumerator = true := by
  decide +kernel
theorem bound440 {x y : ℝ} (h : cell440.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell440 residualNumerator check440 h
def cell439 : Cell := gridCell 64 7 15
theorem check439 : Cell.secondCheck normalizedResidual cell439 residualNumerator = true := by
  decide +kernel
theorem bound439 {x y : ℝ} (h : cell439.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell439 residualNumerator check439 h
def RawShard0031Cells : List Cell := [cell442, cell441, cell440, cell439]
theorem RawShard0031Valid : ValidCells RawShard0031Cells := by
  intro c hc x y h
  simp only [RawShard0031Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h442 | h441 | h440 | h439
  · subst c
    exact bound442 h
  · subst c
    exact bound441 h
  · subst c
    exact bound440 h
  · subst c
    exact bound439 h
#print axioms RawShard0031Valid
end PinnCertFarm
