import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell446 : Cell := gridCell 64 6 12
theorem check446 : Cell.secondCheck normalizedResidual cell446 residualNumerator = true := by
  decide +kernel
theorem bound446 {x y : ℝ} (h : cell446.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell446 residualNumerator check446 h
def cell445 : Cell := gridCell 64 6 13
theorem check445 : Cell.secondCheck normalizedResidual cell445 residualNumerator = true := by
  decide +kernel
theorem bound445 {x y : ℝ} (h : cell445.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell445 residualNumerator check445 h
def cell444 : Cell := gridCell 64 7 12
theorem check444 : Cell.secondCheck normalizedResidual cell444 residualNumerator = true := by
  decide +kernel
theorem bound444 {x y : ℝ} (h : cell444.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell444 residualNumerator check444 h
def cell443 : Cell := gridCell 64 7 13
theorem check443 : Cell.secondCheck normalizedResidual cell443 residualNumerator = true := by
  decide +kernel
theorem bound443 {x y : ℝ} (h : cell443.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell443 residualNumerator check443 h
def RawShard0030Cells : List Cell := [cell446, cell445, cell444, cell443]
theorem RawShard0030Valid : ValidCells RawShard0030Cells := by
  intro c hc x y h
  simp only [RawShard0030Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h446 | h445 | h444 | h443
  · subst c
    exact bound446 h
  · subst c
    exact bound445 h
  · subst c
    exact bound444 h
  · subst c
    exact bound443 h
#print axioms RawShard0030Valid
end PinnCertFarm
