import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell23 : Cell := gridCell 64 2 4
theorem check23 : Cell.secondCheck normalizedResidual cell23 residualNumerator = true := by
  decide +kernel
theorem bound23 {x y : ℝ} (h : cell23.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell23 residualNumerator check23 h
def cell22 : Cell := gridCell 64 2 5
theorem check22 : Cell.secondCheck normalizedResidual cell22 residualNumerator = true := by
  decide +kernel
theorem bound22 {x y : ℝ} (h : cell22.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell22 residualNumerator check22 h
def cell21 : Cell := gridCell 64 3 4
theorem check21 : Cell.secondCheck normalizedResidual cell21 residualNumerator = true := by
  decide +kernel
theorem bound21 {x y : ℝ} (h : cell21.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell21 residualNumerator check21 h
def cell20 : Cell := gridCell 64 3 5
theorem check20 : Cell.secondCheck normalizedResidual cell20 residualNumerator = true := by
  decide +kernel
theorem bound20 {x y : ℝ} (h : cell20.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell20 residualNumerator check20 h
def RawShard0006Cells : List Cell := [cell23, cell22, cell21, cell20]
theorem RawShard0006Valid : ValidCells RawShard0006Cells := by
  intro c hc x y h
  simp only [RawShard0006Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h23 | h22 | h21 | h20
  · subst c
    exact bound23 h
  · subst c
    exact bound22 h
  · subst c
    exact bound21 h
  · subst c
    exact bound20 h
#print axioms RawShard0006Valid
end PinnCertFarm
