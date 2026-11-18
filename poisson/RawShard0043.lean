import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1245 : Cell := gridCell 64 14 2
theorem check1245 : Cell.secondCheck normalizedResidual cell1245 residualNumerator = true := by
  decide +kernel
theorem bound1245 {x y : ℝ} (h : cell1245.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1245 residualNumerator check1245 h
def cell1244 : Cell := gridCell 64 14 3
theorem check1244 : Cell.secondCheck normalizedResidual cell1244 residualNumerator = true := by
  decide +kernel
theorem bound1244 {x y : ℝ} (h : cell1244.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1244 residualNumerator check1244 h
def cell1243 : Cell := gridCell 64 15 2
theorem check1243 : Cell.secondCheck normalizedResidual cell1243 residualNumerator = true := by
  decide +kernel
theorem bound1243 {x y : ℝ} (h : cell1243.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1243 residualNumerator check1243 h
def cell1242 : Cell := gridCell 64 15 3
theorem check1242 : Cell.secondCheck normalizedResidual cell1242 residualNumerator = true := by
  decide +kernel
theorem bound1242 {x y : ℝ} (h : cell1242.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1242 residualNumerator check1242 h
def RawShard0043Cells : List Cell := [cell1245, cell1244, cell1243, cell1242]
theorem RawShard0043Valid : ValidCells RawShard0043Cells := by
  intro c hc x y h
  simp only [RawShard0043Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1245 | h1244 | h1243 | h1242
  · subst c
    exact bound1245 h
  · subst c
    exact bound1244 h
  · subst c
    exact bound1243 h
  · subst c
    exact bound1242 h
#print axioms RawShard0043Valid
end PinnCertFarm
