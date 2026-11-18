import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell75 : Cell := gridCell 64 0 18
theorem check75 : Cell.secondCheck normalizedResidual cell75 residualNumerator = true := by
  decide +kernel
theorem bound75 {x y : ℝ} (h : cell75.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell75 residualNumerator check75 h
def cell74 : Cell := gridCell 64 0 19
theorem check74 : Cell.secondCheck normalizedResidual cell74 residualNumerator = true := by
  decide +kernel
theorem bound74 {x y : ℝ} (h : cell74.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell74 residualNumerator check74 h
def cell73 : Cell := gridCell 64 1 18
theorem check73 : Cell.secondCheck normalizedResidual cell73 residualNumerator = true := by
  decide +kernel
theorem bound73 {x y : ℝ} (h : cell73.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell73 residualNumerator check73 h
def cell72 : Cell := gridCell 64 1 19
theorem check72 : Cell.secondCheck normalizedResidual cell72 residualNumerator = true := by
  decide +kernel
theorem bound72 {x y : ℝ} (h : cell72.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell72 residualNumerator check72 h
def RawShard0065Cells : List Cell := [cell75, cell74, cell73, cell72]
theorem RawShard0065Valid : ValidCells RawShard0065Cells := by
  intro c hc x y h
  simp only [RawShard0065Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h75 | h74 | h73 | h72
  · subst c
    exact bound75 h
  · subst c
    exact bound74 h
  · subst c
    exact bound73 h
  · subst c
    exact bound72 h
#print axioms RawShard0065Valid
end PinnCertFarm
