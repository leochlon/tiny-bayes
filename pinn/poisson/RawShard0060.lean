import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1305 : Cell := gridCell 64 12 12
theorem check1305 : Cell.secondCheck normalizedResidual cell1305 residualNumerator = true := by
  decide +kernel
theorem bound1305 {x y : ℝ} (h : cell1305.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1305 residualNumerator check1305 h
def cell1304 : Cell := gridCell 64 12 13
theorem check1304 : Cell.secondCheck normalizedResidual cell1304 residualNumerator = true := by
  decide +kernel
theorem bound1304 {x y : ℝ} (h : cell1304.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1304 residualNumerator check1304 h
def cell1303 : Cell := gridCell 64 13 12
theorem check1303 : Cell.secondCheck normalizedResidual cell1303 residualNumerator = true := by
  decide +kernel
theorem bound1303 {x y : ℝ} (h : cell1303.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1303 residualNumerator check1303 h
def cell1302 : Cell := gridCell 64 13 13
theorem check1302 : Cell.secondCheck normalizedResidual cell1302 residualNumerator = true := by
  decide +kernel
theorem bound1302 {x y : ℝ} (h : cell1302.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1302 residualNumerator check1302 h
def RawShard0060Cells : List Cell := [cell1305, cell1304, cell1303, cell1302]
theorem RawShard0060Valid : ValidCells RawShard0060Cells := by
  intro c hc x y h
  simp only [RawShard0060Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1305 | h1304 | h1303 | h1302
  · subst c
    exact bound1305 h
  · subst c
    exact bound1304 h
  · subst c
    exact bound1303 h
  · subst c
    exact bound1302 h
#print axioms RawShard0060Valid
end PinnCertFarm
