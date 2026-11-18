import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell43 : Cell := gridCell 64 0 10
theorem check43 : Cell.secondCheck normalizedResidual cell43 residualNumerator = true := by
  decide +kernel
theorem bound43 {x y : ℝ} (h : cell43.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell43 residualNumerator check43 h
def cell42 : Cell := gridCell 64 0 11
theorem check42 : Cell.secondCheck normalizedResidual cell42 residualNumerator = true := by
  decide +kernel
theorem bound42 {x y : ℝ} (h : cell42.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell42 residualNumerator check42 h
def cell41 : Cell := gridCell 64 1 10
theorem check41 : Cell.secondCheck normalizedResidual cell41 residualNumerator = true := by
  decide +kernel
theorem bound41 {x y : ℝ} (h : cell41.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell41 residualNumerator check41 h
def cell40 : Cell := gridCell 64 1 11
theorem check40 : Cell.secondCheck normalizedResidual cell40 residualNumerator = true := by
  decide +kernel
theorem bound40 {x y : ℝ} (h : cell40.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell40 residualNumerator check40 h
def RawShard0017Cells : List Cell := [cell43, cell42, cell41, cell40]
theorem RawShard0017Valid : ValidCells RawShard0017Cells := by
  intro c hc x y h
  simp only [RawShard0017Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h43 | h42 | h41 | h40
  · subst c
    exact bound43 h
  · subst c
    exact bound42 h
  · subst c
    exact bound41 h
  · subst c
    exact bound40 h
#print axioms RawShard0017Valid
end PinnCertFarm
