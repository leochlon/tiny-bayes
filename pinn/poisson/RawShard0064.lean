import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell79 : Cell := gridCell 64 0 16
theorem check79 : Cell.secondCheck normalizedResidual cell79 residualNumerator = true := by
  decide +kernel
theorem bound79 {x y : ℝ} (h : cell79.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell79 residualNumerator check79 h
def cell78 : Cell := gridCell 64 0 17
theorem check78 : Cell.secondCheck normalizedResidual cell78 residualNumerator = true := by
  decide +kernel
theorem bound78 {x y : ℝ} (h : cell78.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell78 residualNumerator check78 h
def cell77 : Cell := gridCell 64 1 16
theorem check77 : Cell.secondCheck normalizedResidual cell77 residualNumerator = true := by
  decide +kernel
theorem bound77 {x y : ℝ} (h : cell77.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell77 residualNumerator check77 h
def cell76 : Cell := gridCell 64 1 17
theorem check76 : Cell.secondCheck normalizedResidual cell76 residualNumerator = true := by
  decide +kernel
theorem bound76 {x y : ℝ} (h : cell76.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell76 residualNumerator check76 h
def RawShard0064Cells : List Cell := [cell79, cell78, cell77, cell76]
theorem RawShard0064Valid : ValidCells RawShard0064Cells := by
  intro c hc x y h
  simp only [RawShard0064Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h79 | h78 | h77 | h76
  · subst c
    exact bound79 h
  · subst c
    exact bound78 h
  · subst c
    exact bound77 h
  · subst c
    exact bound76 h
#print axioms RawShard0064Valid
end PinnCertFarm
