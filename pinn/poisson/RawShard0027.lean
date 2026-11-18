import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell426 : Cell := gridCell 64 6 10
theorem check426 : Cell.secondCheck normalizedResidual cell426 residualNumerator = true := by
  decide +kernel
theorem bound426 {x y : ℝ} (h : cell426.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell426 residualNumerator check426 h
def cell425 : Cell := gridCell 64 6 11
theorem check425 : Cell.secondCheck normalizedResidual cell425 residualNumerator = true := by
  decide +kernel
theorem bound425 {x y : ℝ} (h : cell425.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell425 residualNumerator check425 h
def cell424 : Cell := gridCell 64 7 10
theorem check424 : Cell.secondCheck normalizedResidual cell424 residualNumerator = true := by
  decide +kernel
theorem bound424 {x y : ℝ} (h : cell424.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell424 residualNumerator check424 h
def cell423 : Cell := gridCell 64 7 11
theorem check423 : Cell.secondCheck normalizedResidual cell423 residualNumerator = true := by
  decide +kernel
theorem bound423 {x y : ℝ} (h : cell423.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell423 residualNumerator check423 h
def RawShard0027Cells : List Cell := [cell426, cell425, cell424, cell423]
theorem RawShard0027Valid : ValidCells RawShard0027Cells := by
  intro c hc x y h
  simp only [RawShard0027Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h426 | h425 | h424 | h423
  · subst c
    exact bound426 h
  · subst c
    exact bound425 h
  · subst c
    exact bound424 h
  · subst c
    exact bound423 h
#print axioms RawShard0027Valid
end PinnCertFarm
