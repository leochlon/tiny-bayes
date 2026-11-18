import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1261 : Cell := gridCell 64 14 6
theorem check1261 : Cell.secondCheck normalizedResidual cell1261 residualNumerator = true := by
  decide +kernel
theorem bound1261 {x y : ℝ} (h : cell1261.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1261 residualNumerator check1261 h
def cell1260 : Cell := gridCell 64 14 7
theorem check1260 : Cell.secondCheck normalizedResidual cell1260 residualNumerator = true := by
  decide +kernel
theorem bound1260 {x y : ℝ} (h : cell1260.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1260 residualNumerator check1260 h
def cell1259 : Cell := gridCell 64 15 6
theorem check1259 : Cell.secondCheck normalizedResidual cell1259 residualNumerator = true := by
  decide +kernel
theorem bound1259 {x y : ℝ} (h : cell1259.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1259 residualNumerator check1259 h
def cell1258 : Cell := gridCell 64 15 7
theorem check1258 : Cell.secondCheck normalizedResidual cell1258 residualNumerator = true := by
  decide +kernel
theorem bound1258 {x y : ℝ} (h : cell1258.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1258 residualNumerator check1258 h
def RawShard0047Cells : List Cell := [cell1261, cell1260, cell1259, cell1258]
theorem RawShard0047Valid : ValidCells RawShard0047Cells := by
  intro c hc x y h
  simp only [RawShard0047Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1261 | h1260 | h1259 | h1258
  · subst c
    exact bound1261 h
  · subst c
    exact bound1260 h
  · subst c
    exact bound1259 h
  · subst c
    exact bound1258 h
#print axioms RawShard0047Valid
end PinnCertFarm
