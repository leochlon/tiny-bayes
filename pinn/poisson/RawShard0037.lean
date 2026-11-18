import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell839 : Cell := gridCell 64 8 6
theorem check839 : Cell.secondCheck normalizedResidual cell839 residualNumerator = true := by
  decide +kernel
theorem bound839 {x y : ℝ} (h : cell839.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell839 residualNumerator check839 h
def cell838 : Cell := gridCell 64 8 7
theorem check838 : Cell.secondCheck normalizedResidual cell838 residualNumerator = true := by
  decide +kernel
theorem bound838 {x y : ℝ} (h : cell838.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell838 residualNumerator check838 h
def cell837 : Cell := gridCell 64 9 6
theorem check837 : Cell.secondCheck normalizedResidual cell837 residualNumerator = true := by
  decide +kernel
theorem bound837 {x y : ℝ} (h : cell837.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell837 residualNumerator check837 h
def cell836 : Cell := gridCell 64 9 7
theorem check836 : Cell.secondCheck normalizedResidual cell836 residualNumerator = true := by
  decide +kernel
theorem bound836 {x y : ℝ} (h : cell836.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell836 residualNumerator check836 h
def RawShard0037Cells : List Cell := [cell839, cell838, cell837, cell836]
theorem RawShard0037Valid : ValidCells RawShard0037Cells := by
  intro c hc x y h
  simp only [RawShard0037Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h839 | h838 | h837 | h836
  · subst c
    exact bound839 h
  · subst c
    exact bound838 h
  · subst c
    exact bound837 h
  · subst c
    exact bound836 h
#print axioms RawShard0037Valid
end PinnCertFarm
