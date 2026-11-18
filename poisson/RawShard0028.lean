import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell454 : Cell := gridCell 64 4 12
theorem check454 : Cell.secondCheck normalizedResidual cell454 residualNumerator = true := by
  decide +kernel
theorem bound454 {x y : ℝ} (h : cell454.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell454 residualNumerator check454 h
def cell453 : Cell := gridCell 64 4 13
theorem check453 : Cell.secondCheck normalizedResidual cell453 residualNumerator = true := by
  decide +kernel
theorem bound453 {x y : ℝ} (h : cell453.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell453 residualNumerator check453 h
def cell452 : Cell := gridCell 64 5 12
theorem check452 : Cell.secondCheck normalizedResidual cell452 residualNumerator = true := by
  decide +kernel
theorem bound452 {x y : ℝ} (h : cell452.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell452 residualNumerator check452 h
def cell451 : Cell := gridCell 64 5 13
theorem check451 : Cell.secondCheck normalizedResidual cell451 residualNumerator = true := by
  decide +kernel
theorem bound451 {x y : ℝ} (h : cell451.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell451 residualNumerator check451 h
def RawShard0028Cells : List Cell := [cell454, cell453, cell452, cell451]
theorem RawShard0028Valid : ValidCells RawShard0028Cells := by
  intro c hc x y h
  simp only [RawShard0028Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h454 | h453 | h452 | h451
  · subst c
    exact bound454 h
  · subst c
    exact bound453 h
  · subst c
    exact bound452 h
  · subst c
    exact bound451 h
#print axioms RawShard0028Valid
end PinnCertFarm
