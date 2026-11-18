import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1269 : Cell := gridCell 64 12 6
theorem check1269 : Cell.secondCheck normalizedResidual cell1269 residualNumerator = true := by
  decide +kernel
theorem bound1269 {x y : ℝ} (h : cell1269.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1269 residualNumerator check1269 h
def cell1268 : Cell := gridCell 64 12 7
theorem check1268 : Cell.secondCheck normalizedResidual cell1268 residualNumerator = true := by
  decide +kernel
theorem bound1268 {x y : ℝ} (h : cell1268.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1268 residualNumerator check1268 h
def cell1267 : Cell := gridCell 64 13 6
theorem check1267 : Cell.secondCheck normalizedResidual cell1267 residualNumerator = true := by
  decide +kernel
theorem bound1267 {x y : ℝ} (h : cell1267.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1267 residualNumerator check1267 h
def cell1266 : Cell := gridCell 64 13 7
theorem check1266 : Cell.secondCheck normalizedResidual cell1266 residualNumerator = true := by
  decide +kernel
theorem bound1266 {x y : ℝ} (h : cell1266.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell1266 residualNumerator check1266 h
def RawShard0045Cells : List Cell := [cell1269, cell1268, cell1267, cell1266]
theorem RawShard0045Valid : ValidCells RawShard0045Cells := by
  intro c hc x y h
  simp only [RawShard0045Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1269 | h1268 | h1267 | h1266
  · subst c
    exact bound1269 h
  · subst c
    exact bound1268 h
  · subst c
    exact bound1267 h
  · subst c
    exact bound1266 h
#print axioms RawShard0045Valid
end PinnCertFarm
