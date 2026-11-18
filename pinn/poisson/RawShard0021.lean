import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell59 : Cell := gridCell 64 0 14
theorem check59 : Cell.secondCheck normalizedResidual cell59 residualNumerator = true := by
  decide +kernel
theorem bound59 {x y : ℝ} (h : cell59.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell59 residualNumerator check59 h
def cell58 : Cell := gridCell 64 0 15
theorem check58 : Cell.secondCheck normalizedResidual cell58 residualNumerator = true := by
  decide +kernel
theorem bound58 {x y : ℝ} (h : cell58.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell58 residualNumerator check58 h
def cell57 : Cell := gridCell 64 1 14
theorem check57 : Cell.secondCheck normalizedResidual cell57 residualNumerator = true := by
  decide +kernel
theorem bound57 {x y : ℝ} (h : cell57.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell57 residualNumerator check57 h
def cell56 : Cell := gridCell 64 1 15
theorem check56 : Cell.secondCheck normalizedResidual cell56 residualNumerator = true := by
  decide +kernel
theorem bound56 {x y : ℝ} (h : cell56.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell56 residualNumerator check56 h
def RawShard0021Cells : List Cell := [cell59, cell58, cell57, cell56]
theorem RawShard0021Valid : ValidCells RawShard0021Cells := by
  intro c hc x y h
  simp only [RawShard0021Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h59 | h58 | h57 | h56
  · subst c
    exact bound59 h
  · subst c
    exact bound58 h
  · subst c
    exact bound57 h
  · subst c
    exact bound56 h
#print axioms RawShard0021Valid
end PinnCertFarm
