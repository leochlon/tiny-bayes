import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell35 : Cell := gridCell 64 2 10
theorem check35 : Cell.secondCheck normalizedResidual cell35 residualNumerator = true := by
  decide +kernel
theorem bound35 {x y : ℝ} (h : cell35.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell35 residualNumerator check35 h
def cell34 : Cell := gridCell 64 2 11
theorem check34 : Cell.secondCheck normalizedResidual cell34 residualNumerator = true := by
  decide +kernel
theorem bound34 {x y : ℝ} (h : cell34.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell34 residualNumerator check34 h
def cell33 : Cell := gridCell 64 3 10
theorem check33 : Cell.secondCheck normalizedResidual cell33 residualNumerator = true := by
  decide +kernel
theorem bound33 {x y : ℝ} (h : cell33.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell33 residualNumerator check33 h
def cell32 : Cell := gridCell 64 3 11
theorem check32 : Cell.secondCheck normalizedResidual cell32 residualNumerator = true := by
  decide +kernel
theorem bound32 {x y : ℝ} (h : cell32.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell32 residualNumerator check32 h
def RawShard0019Cells : List Cell := [cell35, cell34, cell33, cell32]
theorem RawShard0019Valid : ValidCells RawShard0019Cells := by
  intro c hc x y h
  simp only [RawShard0019Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h35 | h34 | h33 | h32
  · subst c
    exact bound35 h
  · subst c
    exact bound34 h
  · subst c
    exact bound33 h
  · subst c
    exact bound32 h
#print axioms RawShard0019Valid
end PinnCertFarm
