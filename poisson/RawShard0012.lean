import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell422 : Cell := gridCell 64 4 4
theorem check422 : Cell.secondCheck normalizedResidual cell422 residualNumerator = true := by
  decide +kernel
theorem bound422 {x y : ℝ} (h : cell422.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell422 residualNumerator check422 h
def cell421 : Cell := gridCell 64 4 5
theorem check421 : Cell.secondCheck normalizedResidual cell421 residualNumerator = true := by
  decide +kernel
theorem bound421 {x y : ℝ} (h : cell421.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell421 residualNumerator check421 h
def cell420 : Cell := gridCell 64 5 4
theorem check420 : Cell.secondCheck normalizedResidual cell420 residualNumerator = true := by
  decide +kernel
theorem bound420 {x y : ℝ} (h : cell420.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell420 residualNumerator check420 h
def cell419 : Cell := gridCell 64 5 5
theorem check419 : Cell.secondCheck normalizedResidual cell419 residualNumerator = true := by
  decide +kernel
theorem bound419 {x y : ℝ} (h : cell419.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell419 residualNumerator check419 h
def RawShard0012Cells : List Cell := [cell422, cell421, cell420, cell419]
theorem RawShard0012Valid : ValidCells RawShard0012Cells := by
  intro c hc x y h
  simp only [RawShard0012Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h422 | h421 | h420 | h419
  · subst c
    exact bound422 h
  · subst c
    exact bound421 h
  · subst c
    exact bound420 h
  · subst c
    exact bound419 h
#print axioms RawShard0012Valid
end PinnCertFarm
