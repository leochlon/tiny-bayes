import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell823 : Cell := gridCell 64 8 2
theorem check823 : Cell.secondCheck normalizedResidual cell823 residualNumerator = true := by
  decide +kernel
theorem bound823 {x y : ℝ} (h : cell823.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell823 residualNumerator check823 h
def cell822 : Cell := gridCell 64 8 3
theorem check822 : Cell.secondCheck normalizedResidual cell822 residualNumerator = true := by
  decide +kernel
theorem bound822 {x y : ℝ} (h : cell822.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell822 residualNumerator check822 h
def cell821 : Cell := gridCell 64 9 2
theorem check821 : Cell.secondCheck normalizedResidual cell821 residualNumerator = true := by
  decide +kernel
theorem bound821 {x y : ℝ} (h : cell821.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell821 residualNumerator check821 h
def cell820 : Cell := gridCell 64 9 3
theorem check820 : Cell.secondCheck normalizedResidual cell820 residualNumerator = true := by
  decide +kernel
theorem bound820 {x y : ℝ} (h : cell820.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell820 residualNumerator check820 h
def RawShard0033Cells : List Cell := [cell823, cell822, cell821, cell820]
theorem RawShard0033Valid : ValidCells RawShard0033Cells := by
  intro c hc x y h
  simp only [RawShard0033Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h823 | h822 | h821 | h820
  · subst c
    exact bound823 h
  · subst c
    exact bound822 h
  · subst c
    exact bound821 h
  · subst c
    exact bound820 h
#print axioms RawShard0033Valid
end PinnCertFarm
