import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell851 : Cell := gridCell 64 10 8
theorem check851 : Cell.secondCheck normalizedResidual cell851 residualNumerator = true := by
  decide +kernel
theorem bound851 {x y : ℝ} (h : cell851.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell851 residualNumerator check851 h
def cell850 : Cell := gridCell 64 10 9
theorem check850 : Cell.secondCheck normalizedResidual cell850 residualNumerator = true := by
  decide +kernel
theorem bound850 {x y : ℝ} (h : cell850.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell850 residualNumerator check850 h
def cell849 : Cell := gridCell 64 11 8
theorem check849 : Cell.secondCheck normalizedResidual cell849 residualNumerator = true := by
  decide +kernel
theorem bound849 {x y : ℝ} (h : cell849.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell849 residualNumerator check849 h
def cell848 : Cell := gridCell 64 11 9
theorem check848 : Cell.secondCheck normalizedResidual cell848 residualNumerator = true := by
  decide +kernel
theorem bound848 {x y : ℝ} (h : cell848.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell848 residualNumerator check848 h
def RawShard0050Cells : List Cell := [cell851, cell850, cell849, cell848]
theorem RawShard0050Valid : ValidCells RawShard0050Cells := by
  intro c hc x y h
  simp only [RawShard0050Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h851 | h850 | h849 | h848
  · subst c
    exact bound851 h
  · subst c
    exact bound850 h
  · subst c
    exact bound849 h
  · subst c
    exact bound848 h
#print axioms RawShard0050Valid
end PinnCertFarm
