import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell434 : Cell := gridCell 64 4 10
theorem check434 : Cell.secondCheck normalizedResidual cell434 residualNumerator = true := by
  decide +kernel
theorem bound434 {x y : ℝ} (h : cell434.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell434 residualNumerator check434 h
def cell433 : Cell := gridCell 64 4 11
theorem check433 : Cell.secondCheck normalizedResidual cell433 residualNumerator = true := by
  decide +kernel
theorem bound433 {x y : ℝ} (h : cell433.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell433 residualNumerator check433 h
def cell432 : Cell := gridCell 64 5 10
theorem check432 : Cell.secondCheck normalizedResidual cell432 residualNumerator = true := by
  decide +kernel
theorem bound432 {x y : ℝ} (h : cell432.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell432 residualNumerator check432 h
def cell431 : Cell := gridCell 64 5 11
theorem check431 : Cell.secondCheck normalizedResidual cell431 residualNumerator = true := by
  decide +kernel
theorem bound431 {x y : ℝ} (h : cell431.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell431 residualNumerator check431 h
def RawShard0025Cells : List Cell := [cell434, cell433, cell432, cell431]
theorem RawShard0025Valid : ValidCells RawShard0025Cells := by
  intro c hc x y h
  simp only [RawShard0025Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h434 | h433 | h432 | h431
  · subst c
    exact bound434 h
  · subst c
    exact bound433 h
  · subst c
    exact bound432 h
  · subst c
    exact bound431 h
#print axioms RawShard0025Valid
end PinnCertFarm
