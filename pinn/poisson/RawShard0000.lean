import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell15 : Cell := gridCell 64 0 0
theorem check15 : Cell.secondCheck normalizedResidual cell15 residualNumerator = true := by
  decide +kernel
theorem bound15 {x y : ℝ} (h : cell15.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell15 residualNumerator check15 h
def cell14 : Cell := gridCell 64 0 1
theorem check14 : Cell.secondCheck normalizedResidual cell14 residualNumerator = true := by
  decide +kernel
theorem bound14 {x y : ℝ} (h : cell14.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell14 residualNumerator check14 h
def cell13 : Cell := gridCell 64 1 0
theorem check13 : Cell.secondCheck normalizedResidual cell13 residualNumerator = true := by
  decide +kernel
theorem bound13 {x y : ℝ} (h : cell13.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell13 residualNumerator check13 h
def cell12 : Cell := gridCell 64 1 1
theorem check12 : Cell.secondCheck normalizedResidual cell12 residualNumerator = true := by
  decide +kernel
theorem bound12 {x y : ℝ} (h : cell12.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell12 residualNumerator check12 h
def RawShard0000Cells : List Cell := [cell15, cell14, cell13, cell12]
theorem RawShard0000Valid : ValidCells RawShard0000Cells := by
  intro c hc x y h
  simp only [RawShard0000Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h15 | h14 | h13 | h12
  · subst c
    exact bound15 h
  · subst c
    exact bound14 h
  · subst c
    exact bound13 h
  · subst c
    exact bound12 h
#print axioms RawShard0000Valid
end PinnCertFarm
