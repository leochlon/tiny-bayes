import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell430 : Cell := gridCell 64 6 8
theorem check430 : Cell.secondCheck normalizedResidual cell430 residualNumerator = true := by
  decide +kernel
theorem bound430 {x y : ℝ} (h : cell430.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell430 residualNumerator check430 h
def cell429 : Cell := gridCell 64 6 9
theorem check429 : Cell.secondCheck normalizedResidual cell429 residualNumerator = true := by
  decide +kernel
theorem bound429 {x y : ℝ} (h : cell429.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell429 residualNumerator check429 h
def cell428 : Cell := gridCell 64 7 8
theorem check428 : Cell.secondCheck normalizedResidual cell428 residualNumerator = true := by
  decide +kernel
theorem bound428 {x y : ℝ} (h : cell428.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell428 residualNumerator check428 h
def cell427 : Cell := gridCell 64 7 9
theorem check427 : Cell.secondCheck normalizedResidual cell427 residualNumerator = true := by
  decide +kernel
theorem bound427 {x y : ℝ} (h : cell427.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell427 residualNumerator check427 h
def RawShard0026Cells : List Cell := [cell430, cell429, cell428, cell427]
theorem RawShard0026Valid : ValidCells RawShard0026Cells := by
  intro c hc x y h
  simp only [RawShard0026Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h430 | h429 | h428 | h427
  · subst c
    exact bound430 h
  · subst c
    exact bound429 h
  · subst c
    exact bound428 h
  · subst c
    exact bound427 h
#print axioms RawShard0026Valid
end PinnCertFarm
