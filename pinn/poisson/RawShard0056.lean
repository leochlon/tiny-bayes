import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1289 : Cell := gridCell 64 12 8
theorem check1289 : Cell.secondCheck normalizedResidual cell1289 residualNumerator = true := by
  decide +kernel
theorem bound1289 {x y : ℝ} (h : cell1289.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1289 residualNumerator check1289 h
def cell1288 : Cell := gridCell 64 12 9
theorem check1288 : Cell.secondCheck normalizedResidual cell1288 residualNumerator = true := by
  decide +kernel
theorem bound1288 {x y : ℝ} (h : cell1288.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1288 residualNumerator check1288 h
def cell1287 : Cell := gridCell 64 13 8
theorem check1287 : Cell.secondCheck normalizedResidual cell1287 residualNumerator = true := by
  decide +kernel
theorem bound1287 {x y : ℝ} (h : cell1287.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1287 residualNumerator check1287 h
def cell1286 : Cell := gridCell 64 13 9
theorem check1286 : Cell.secondCheck normalizedResidual cell1286 residualNumerator = true := by
  decide +kernel
theorem bound1286 {x y : ℝ} (h : cell1286.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1286 residualNumerator check1286 h
def RawShard0056Cells : List Cell := [cell1289, cell1288, cell1287, cell1286]
theorem RawShard0056Valid : ValidCells RawShard0056Cells := by
  intro c hc x y h
  simp only [RawShard0056Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1289 | h1288 | h1287 | h1286
  · subst c
    exact bound1289 h
  · subst c
    exact bound1288 h
  · subst c
    exact bound1287 h
  · subst c
    exact bound1286 h
#print axioms RawShard0056Valid
end PinnCertFarm
