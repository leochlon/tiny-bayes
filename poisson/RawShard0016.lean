import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell47 : Cell := gridCell 64 0 8
theorem check47 : Cell.secondCheck normalizedResidual cell47 residualNumerator = true := by
  decide +kernel
theorem bound47 {x y : ℝ} (h : cell47.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell47 residualNumerator check47 h
def cell46 : Cell := gridCell 64 0 9
theorem check46 : Cell.secondCheck normalizedResidual cell46 residualNumerator = true := by
  decide +kernel
theorem bound46 {x y : ℝ} (h : cell46.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell46 residualNumerator check46 h
def cell45 : Cell := gridCell 64 1 8
theorem check45 : Cell.secondCheck normalizedResidual cell45 residualNumerator = true := by
  decide +kernel
theorem bound45 {x y : ℝ} (h : cell45.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell45 residualNumerator check45 h
def cell44 : Cell := gridCell 64 1 9
theorem check44 : Cell.secondCheck normalizedResidual cell44 residualNumerator = true := by
  decide +kernel
theorem bound44 {x y : ℝ} (h : cell44.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell44 residualNumerator check44 h
def RawShard0016Cells : List Cell := [cell47, cell46, cell45, cell44]
theorem RawShard0016Valid : ValidCells RawShard0016Cells := by
  intro c hc x y h
  simp only [RawShard0016Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h47 | h46 | h45 | h44
  · subst c
    exact bound47 h
  · subst c
    exact bound46 h
  · subst c
    exact bound45 h
  · subst c
    exact bound44 h
#print axioms RawShard0016Valid
end PinnCertFarm
