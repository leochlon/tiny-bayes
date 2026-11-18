import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3 : Cell := gridCell 64 2 2
theorem check3 : Cell.secondCheck normalizedResidual cell3 residualNumerator = true := by
  decide +kernel
theorem bound3 {x y : ℝ} (h : cell3.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell3 residualNumerator check3 h
def cell2 : Cell := gridCell 64 2 3
theorem check2 : Cell.secondCheck normalizedResidual cell2 residualNumerator = true := by
  decide +kernel
theorem bound2 {x y : ℝ} (h : cell2.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell2 residualNumerator check2 h
def cell1 : Cell := gridCell 64 3 2
theorem check1 : Cell.secondCheck normalizedResidual cell1 residualNumerator = true := by
  decide +kernel
theorem bound1 {x y : ℝ} (h : cell1.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1 residualNumerator check1 h
def cell0 : Cell := gridCell 64 3 3
theorem check0 : Cell.secondCheck normalizedResidual cell0 residualNumerator = true := by
  decide +kernel
theorem bound0 {x y : ℝ} (h : cell0.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell0 residualNumerator check0 h
def RawShard0003Cells : List Cell := [cell3, cell2, cell1, cell0]
theorem RawShard0003Valid : ValidCells RawShard0003Cells := by
  intro c hc x y h
  simp only [RawShard0003Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3 | h2 | h1 | h0
  · subst c
    exact bound3 h
  · subst c
    exact bound2 h
  · subst c
    exact bound1 h
  · subst c
    exact bound0 h
#print axioms RawShard0003Valid
end PinnCertFarm
