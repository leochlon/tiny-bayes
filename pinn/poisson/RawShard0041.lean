import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1253 : Cell := gridCell 64 12 2
theorem check1253 : Cell.secondCheck normalizedResidual cell1253 residualNumerator = true := by
  decide +kernel
theorem bound1253 {x y : ℝ} (h : cell1253.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1253 residualNumerator check1253 h
def cell1252 : Cell := gridCell 64 12 3
theorem check1252 : Cell.secondCheck normalizedResidual cell1252 residualNumerator = true := by
  decide +kernel
theorem bound1252 {x y : ℝ} (h : cell1252.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1252 residualNumerator check1252 h
def cell1251 : Cell := gridCell 64 13 2
theorem check1251 : Cell.secondCheck normalizedResidual cell1251 residualNumerator = true := by
  decide +kernel
theorem bound1251 {x y : ℝ} (h : cell1251.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1251 residualNumerator check1251 h
def cell1250 : Cell := gridCell 64 13 3
theorem check1250 : Cell.secondCheck normalizedResidual cell1250 residualNumerator = true := by
  decide +kernel
theorem bound1250 {x y : ℝ} (h : cell1250.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1250 residualNumerator check1250 h
def RawShard0041Cells : List Cell := [cell1253, cell1252, cell1251, cell1250]
theorem RawShard0041Valid : ValidCells RawShard0041Cells := by
  intro c hc x y h
  simp only [RawShard0041Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1253 | h1252 | h1251 | h1250
  · subst c
    exact bound1253 h
  · subst c
    exact bound1252 h
  · subst c
    exact bound1251 h
  · subst c
    exact bound1250 h
#print axioms RawShard0041Valid
end PinnCertFarm
