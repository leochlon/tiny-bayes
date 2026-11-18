import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell31 : Cell := gridCell 64 0 4
theorem check31 : Cell.secondCheck normalizedResidual cell31 residualNumerator = true := by
  decide +kernel
theorem bound31 {x y : ℝ} (h : cell31.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell31 residualNumerator check31 h
def cell30 : Cell := gridCell 64 0 5
theorem check30 : Cell.secondCheck normalizedResidual cell30 residualNumerator = true := by
  decide +kernel
theorem bound30 {x y : ℝ} (h : cell30.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell30 residualNumerator check30 h
def cell29 : Cell := gridCell 64 1 4
theorem check29 : Cell.secondCheck normalizedResidual cell29 residualNumerator = true := by
  decide +kernel
theorem bound29 {x y : ℝ} (h : cell29.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell29 residualNumerator check29 h
def cell28 : Cell := gridCell 64 1 5
theorem check28 : Cell.secondCheck normalizedResidual cell28 residualNumerator = true := by
  decide +kernel
theorem bound28 {x y : ℝ} (h : cell28.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell28 residualNumerator check28 h
def RawShard0004Cells : List Cell := [cell31, cell30, cell29, cell28]
theorem RawShard0004Valid : ValidCells RawShard0004Cells := by
  intro c hc x y h
  simp only [RawShard0004Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h31 | h30 | h29 | h28
  · subst c
    exact bound31 h
  · subst c
    exact bound30 h
  · subst c
    exact bound29 h
  · subst c
    exact bound28 h
#print axioms RawShard0004Valid
end PinnCertFarm
