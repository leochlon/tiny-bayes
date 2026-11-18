import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell867 : Cell := gridCell 64 10 12
theorem check867 : Cell.secondCheck normalizedResidual cell867 residualNumerator = true := by
  decide +kernel
theorem bound867 {x y : ℝ} (h : cell867.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell867 residualNumerator check867 h
def cell866 : Cell := gridCell 64 10 13
theorem check866 : Cell.secondCheck normalizedResidual cell866 residualNumerator = true := by
  decide +kernel
theorem bound866 {x y : ℝ} (h : cell866.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell866 residualNumerator check866 h
def cell865 : Cell := gridCell 64 11 12
theorem check865 : Cell.secondCheck normalizedResidual cell865 residualNumerator = true := by
  decide +kernel
theorem bound865 {x y : ℝ} (h : cell865.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell865 residualNumerator check865 h
def cell864 : Cell := gridCell 64 11 13
theorem check864 : Cell.secondCheck normalizedResidual cell864 residualNumerator = true := by
  decide +kernel
theorem bound864 {x y : ℝ} (h : cell864.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell864 residualNumerator check864 h
def RawShard0054Cells : List Cell := [cell867, cell866, cell865, cell864]
theorem RawShard0054Valid : ValidCells RawShard0054Cells := by
  intro c hc x y h
  simp only [RawShard0054Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h867 | h866 | h865 | h864
  · subst c
    exact bound867 h
  · subst c
    exact bound866 h
  · subst c
    exact bound865 h
  · subst c
    exact bound864 h
#print axioms RawShard0054Valid
end PinnCertFarm
