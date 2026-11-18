import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell27 : Cell := gridCell 64 0 6
theorem check27 : Cell.secondCheck normalizedResidual cell27 residualNumerator = true := by
  decide +kernel
theorem bound27 {x y : ℝ} (h : cell27.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell27 residualNumerator check27 h
def cell26 : Cell := gridCell 64 0 7
theorem check26 : Cell.secondCheck normalizedResidual cell26 residualNumerator = true := by
  decide +kernel
theorem bound26 {x y : ℝ} (h : cell26.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell26 residualNumerator check26 h
def cell25 : Cell := gridCell 64 1 6
theorem check25 : Cell.secondCheck normalizedResidual cell25 residualNumerator = true := by
  decide +kernel
theorem bound25 {x y : ℝ} (h : cell25.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell25 residualNumerator check25 h
def cell24 : Cell := gridCell 64 1 7
theorem check24 : Cell.secondCheck normalizedResidual cell24 residualNumerator = true := by
  decide +kernel
theorem bound24 {x y : ℝ} (h : cell24.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell24 residualNumerator check24 h
def RawShard0005Cells : List Cell := [cell27, cell26, cell25, cell24]
theorem RawShard0005Valid : ValidCells RawShard0005Cells := by
  intro c hc x y h
  simp only [RawShard0005Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h27 | h26 | h25 | h24
  · subst c
    exact bound27 h
  · subst c
    exact bound26 h
  · subst c
    exact bound25 h
  · subst c
    exact bound24 h
#print axioms RawShard0005Valid
end PinnCertFarm
