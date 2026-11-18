import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell63 : Cell := gridCell 64 0 12
theorem check63 : Cell.secondCheck normalizedResidual cell63 residualNumerator = true := by
  decide +kernel
theorem bound63 {x y : ℝ} (h : cell63.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell63 residualNumerator check63 h
def cell62 : Cell := gridCell 64 0 13
theorem check62 : Cell.secondCheck normalizedResidual cell62 residualNumerator = true := by
  decide +kernel
theorem bound62 {x y : ℝ} (h : cell62.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell62 residualNumerator check62 h
def cell61 : Cell := gridCell 64 1 12
theorem check61 : Cell.secondCheck normalizedResidual cell61 residualNumerator = true := by
  decide +kernel
theorem bound61 {x y : ℝ} (h : cell61.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell61 residualNumerator check61 h
def cell60 : Cell := gridCell 64 1 13
theorem check60 : Cell.secondCheck normalizedResidual cell60 residualNumerator = true := by
  decide +kernel
theorem bound60 {x y : ℝ} (h : cell60.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell60 residualNumerator check60 h
def RawShard0020Cells : List Cell := [cell63, cell62, cell61, cell60]
theorem RawShard0020Valid : ValidCells RawShard0020Cells := by
  intro c hc x y h
  simp only [RawShard0020Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h63 | h62 | h61 | h60
  · subst c
    exact bound63 h
  · subst c
    exact bound62 h
  · subst c
    exact bound61 h
  · subst c
    exact bound60 h
#print axioms RawShard0020Valid
end PinnCertFarm
