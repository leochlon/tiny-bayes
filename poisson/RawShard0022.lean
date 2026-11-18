import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell55 : Cell := gridCell 64 2 12
theorem check55 : Cell.secondCheck normalizedResidual cell55 residualNumerator = true := by
  decide +kernel
theorem bound55 {x y : ℝ} (h : cell55.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell55 residualNumerator check55 h
def cell54 : Cell := gridCell 64 2 13
theorem check54 : Cell.secondCheck normalizedResidual cell54 residualNumerator = true := by
  decide +kernel
theorem bound54 {x y : ℝ} (h : cell54.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell54 residualNumerator check54 h
def cell53 : Cell := gridCell 64 3 12
theorem check53 : Cell.secondCheck normalizedResidual cell53 residualNumerator = true := by
  decide +kernel
theorem bound53 {x y : ℝ} (h : cell53.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell53 residualNumerator check53 h
def cell52 : Cell := gridCell 64 3 13
theorem check52 : Cell.secondCheck normalizedResidual cell52 residualNumerator = true := by
  decide +kernel
theorem bound52 {x y : ℝ} (h : cell52.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell52 residualNumerator check52 h
def RawShard0022Cells : List Cell := [cell55, cell54, cell53, cell52]
theorem RawShard0022Valid : ValidCells RawShard0022Cells := by
  intro c hc x y h
  simp only [RawShard0022Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h55 | h54 | h53 | h52
  · subst c
    exact bound55 h
  · subst c
    exact bound54 h
  · subst c
    exact bound53 h
  · subst c
    exact bound52 h
#print axioms RawShard0022Valid
end PinnCertFarm
