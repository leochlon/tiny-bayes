import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1257 : Cell := gridCell 64 12 0
theorem check1257 : Cell.secondCheck normalizedResidual cell1257 residualNumerator = true := by
  decide +kernel
theorem bound1257 {x y : ℝ} (h : cell1257.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1257 residualNumerator check1257 h
def cell1256 : Cell := gridCell 64 12 1
theorem check1256 : Cell.secondCheck normalizedResidual cell1256 residualNumerator = true := by
  decide +kernel
theorem bound1256 {x y : ℝ} (h : cell1256.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1256 residualNumerator check1256 h
def cell1255 : Cell := gridCell 64 13 0
theorem check1255 : Cell.secondCheck normalizedResidual cell1255 residualNumerator = true := by
  decide +kernel
theorem bound1255 {x y : ℝ} (h : cell1255.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1255 residualNumerator check1255 h
def cell1254 : Cell := gridCell 64 13 1
theorem check1254 : Cell.secondCheck normalizedResidual cell1254 residualNumerator = true := by
  decide +kernel
theorem bound1254 {x y : ℝ} (h : cell1254.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1254 residualNumerator check1254 h
def RawShard0040Cells : List Cell := [cell1257, cell1256, cell1255, cell1254]
theorem RawShard0040Valid : ValidCells RawShard0040Cells := by
  intro c hc x y h
  simp only [RawShard0040Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1257 | h1256 | h1255 | h1254
  · subst c
    exact bound1257 h
  · subst c
    exact bound1256 h
  · subst c
    exact bound1255 h
  · subst c
    exact bound1254 h
#print axioms RawShard0040Valid
end PinnCertFarm
