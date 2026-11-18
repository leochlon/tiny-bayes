import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1265 : Cell := gridCell 64 14 4
theorem check1265 : Cell.secondCheck normalizedResidual cell1265 residualNumerator = true := by
  decide +kernel
theorem bound1265 {x y : ℝ} (h : cell1265.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1265 residualNumerator check1265 h
def cell1264 : Cell := gridCell 64 14 5
theorem check1264 : Cell.secondCheck normalizedResidual cell1264 residualNumerator = true := by
  decide +kernel
theorem bound1264 {x y : ℝ} (h : cell1264.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1264 residualNumerator check1264 h
def cell1263 : Cell := gridCell 64 15 4
theorem check1263 : Cell.secondCheck normalizedResidual cell1263 residualNumerator = true := by
  decide +kernel
theorem bound1263 {x y : ℝ} (h : cell1263.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1263 residualNumerator check1263 h
def cell1262 : Cell := gridCell 64 15 5
theorem check1262 : Cell.secondCheck normalizedResidual cell1262 residualNumerator = true := by
  decide +kernel
theorem bound1262 {x y : ℝ} (h : cell1262.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1262 residualNumerator check1262 h
def RawShard0046Cells : List Cell := [cell1265, cell1264, cell1263, cell1262]
theorem RawShard0046Valid : ValidCells RawShard0046Cells := by
  intro c hc x y h
  simp only [RawShard0046Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1265 | h1264 | h1263 | h1262
  · subst c
    exact bound1265 h
  · subst c
    exact bound1264 h
  · subst c
    exact bound1263 h
  · subst c
    exact bound1262 h
#print axioms RawShard0046Valid
end PinnCertFarm
