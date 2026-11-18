import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell394 : Cell := gridCell 64 6 2
theorem check394 : Cell.secondCheck normalizedResidual cell394 residualNumerator = true := by
  decide +kernel
theorem bound394 {x y : ℝ} (h : cell394.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell394 residualNumerator check394 h
def cell393 : Cell := gridCell 64 6 3
theorem check393 : Cell.secondCheck normalizedResidual cell393 residualNumerator = true := by
  decide +kernel
theorem bound393 {x y : ℝ} (h : cell393.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell393 residualNumerator check393 h
def cell392 : Cell := gridCell 64 7 2
theorem check392 : Cell.secondCheck normalizedResidual cell392 residualNumerator = true := by
  decide +kernel
theorem bound392 {x y : ℝ} (h : cell392.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell392 residualNumerator check392 h
def cell391 : Cell := gridCell 64 7 3
theorem check391 : Cell.secondCheck normalizedResidual cell391 residualNumerator = true := by
  decide +kernel
theorem bound391 {x y : ℝ} (h : cell391.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell391 residualNumerator check391 h
def RawShard0011Cells : List Cell := [cell394, cell393, cell392, cell391]
theorem RawShard0011Valid : ValidCells RawShard0011Cells := by
  intro c hc x y h
  simp only [RawShard0011Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h394 | h393 | h392 | h391
  · subst c
    exact bound394 h
  · subst c
    exact bound393 h
  · subst c
    exact bound392 h
  · subst c
    exact bound391 h
#print axioms RawShard0011Valid
end PinnCertFarm
