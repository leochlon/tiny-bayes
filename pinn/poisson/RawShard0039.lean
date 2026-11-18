import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell831 : Cell := gridCell 64 10 6
theorem check831 : Cell.secondCheck normalizedResidual cell831 residualNumerator = true := by
  decide +kernel
theorem bound831 {x y : ℝ} (h : cell831.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell831 residualNumerator check831 h
def cell830 : Cell := gridCell 64 10 7
theorem check830 : Cell.secondCheck normalizedResidual cell830 residualNumerator = true := by
  decide +kernel
theorem bound830 {x y : ℝ} (h : cell830.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell830 residualNumerator check830 h
def cell829 : Cell := gridCell 64 11 6
theorem check829 : Cell.secondCheck normalizedResidual cell829 residualNumerator = true := by
  decide +kernel
theorem bound829 {x y : ℝ} (h : cell829.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell829 residualNumerator check829 h
def cell828 : Cell := gridCell 64 11 7
theorem check828 : Cell.secondCheck normalizedResidual cell828 residualNumerator = true := by
  decide +kernel
theorem bound828 {x y : ℝ} (h : cell828.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell828 residualNumerator check828 h
def RawShard0039Cells : List Cell := [cell831, cell830, cell829, cell828]
theorem RawShard0039Valid : ValidCells RawShard0039Cells := by
  intro c hc x y h
  simp only [RawShard0039Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h831 | h830 | h829 | h828
  · subst c
    exact bound831 h
  · subst c
    exact bound830 h
  · subst c
    exact bound829 h
  · subst c
    exact bound828 h
#print axioms RawShard0039Valid
end PinnCertFarm
