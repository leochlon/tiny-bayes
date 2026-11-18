import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1285 : Cell := gridCell 64 12 10
theorem check1285 : Cell.secondCheck normalizedResidual cell1285 residualNumerator = true := by
  decide +kernel
theorem bound1285 {x y : ℝ} (h : cell1285.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1285 residualNumerator check1285 h
def cell1284 : Cell := gridCell 64 12 11
theorem check1284 : Cell.secondCheck normalizedResidual cell1284 residualNumerator = true := by
  decide +kernel
theorem bound1284 {x y : ℝ} (h : cell1284.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1284 residualNumerator check1284 h
def cell1283 : Cell := gridCell 64 13 10
theorem check1283 : Cell.secondCheck normalizedResidual cell1283 residualNumerator = true := by
  decide +kernel
theorem bound1283 {x y : ℝ} (h : cell1283.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1283 residualNumerator check1283 h
def cell1282 : Cell := gridCell 64 13 11
theorem check1282 : Cell.secondCheck normalizedResidual cell1282 residualNumerator = true := by
  decide +kernel
theorem bound1282 {x y : ℝ} (h : cell1282.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1282 residualNumerator check1282 h
def RawShard0057Cells : List Cell := [cell1285, cell1284, cell1283, cell1282]
theorem RawShard0057Valid : ValidCells RawShard0057Cells := by
  intro c hc x y h
  simp only [RawShard0057Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1285 | h1284 | h1283 | h1282
  · subst c
    exact bound1285 h
  · subst c
    exact bound1284 h
  · subst c
    exact bound1283 h
  · subst c
    exact bound1282 h
#print axioms RawShard0057Valid
end PinnCertFarm
