import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell827 : Cell := gridCell 64 8 0
theorem check827 : Cell.secondCheck normalizedResidual cell827 residualNumerator = true := by
  decide +kernel
theorem bound827 {x y : ℝ} (h : cell827.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell827 residualNumerator check827 h
def cell826 : Cell := gridCell 64 8 1
theorem check826 : Cell.secondCheck normalizedResidual cell826 residualNumerator = true := by
  decide +kernel
theorem bound826 {x y : ℝ} (h : cell826.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell826 residualNumerator check826 h
def cell825 : Cell := gridCell 64 9 0
theorem check825 : Cell.secondCheck normalizedResidual cell825 residualNumerator = true := by
  decide +kernel
theorem bound825 {x y : ℝ} (h : cell825.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell825 residualNumerator check825 h
def cell824 : Cell := gridCell 64 9 1
theorem check824 : Cell.secondCheck normalizedResidual cell824 residualNumerator = true := by
  decide +kernel
theorem bound824 {x y : ℝ} (h : cell824.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell824 residualNumerator check824 h
def RawShard0032Cells : List Cell := [cell827, cell826, cell825, cell824]
theorem RawShard0032Valid : ValidCells RawShard0032Cells := by
  intro c hc x y h
  simp only [RawShard0032Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h827 | h826 | h825 | h824
  · subst c
    exact bound827 h
  · subst c
    exact bound826 h
  · subst c
    exact bound825 h
  · subst c
    exact bound824 h
#print axioms RawShard0032Valid
end PinnCertFarm
