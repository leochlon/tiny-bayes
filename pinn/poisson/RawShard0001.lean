import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell11 : Cell := gridCell 64 0 2
theorem check11 : Cell.secondCheck normalizedResidual cell11 residualNumerator = true := by
  decide +kernel
theorem bound11 {x y : ℝ} (h : cell11.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell11 residualNumerator check11 h
def cell10 : Cell := gridCell 64 0 3
theorem check10 : Cell.secondCheck normalizedResidual cell10 residualNumerator = true := by
  decide +kernel
theorem bound10 {x y : ℝ} (h : cell10.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell10 residualNumerator check10 h
def cell9 : Cell := gridCell 64 1 2
theorem check9 : Cell.secondCheck normalizedResidual cell9 residualNumerator = true := by
  decide +kernel
theorem bound9 {x y : ℝ} (h : cell9.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell9 residualNumerator check9 h
def cell8 : Cell := gridCell 64 1 3
theorem check8 : Cell.secondCheck normalizedResidual cell8 residualNumerator = true := by
  decide +kernel
theorem bound8 {x y : ℝ} (h : cell8.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell8 residualNumerator check8 h
def RawShard0001Cells : List Cell := [cell11, cell10, cell9, cell8]
theorem RawShard0001Valid : ValidCells RawShard0001Cells := by
  intro c hc x y h
  simp only [RawShard0001Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h11 | h10 | h9 | h8
  · subst c
    exact bound11 h
  · subst c
    exact bound10 h
  · subst c
    exact bound9 h
  · subst c
    exact bound8 h
#print axioms RawShard0001Valid
end PinnCertFarm
