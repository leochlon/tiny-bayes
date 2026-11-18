import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell875 : Cell := gridCell 64 8 12
theorem check875 : Cell.secondCheck normalizedResidual cell875 residualNumerator = true := by
  decide +kernel
theorem bound875 {x y : ℝ} (h : cell875.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell875 residualNumerator check875 h
def cell874 : Cell := gridCell 64 8 13
theorem check874 : Cell.secondCheck normalizedResidual cell874 residualNumerator = true := by
  decide +kernel
theorem bound874 {x y : ℝ} (h : cell874.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell874 residualNumerator check874 h
def cell873 : Cell := gridCell 64 9 12
theorem check873 : Cell.secondCheck normalizedResidual cell873 residualNumerator = true := by
  decide +kernel
theorem bound873 {x y : ℝ} (h : cell873.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell873 residualNumerator check873 h
def cell872 : Cell := gridCell 64 9 13
theorem check872 : Cell.secondCheck normalizedResidual cell872 residualNumerator = true := by
  decide +kernel
theorem bound872 {x y : ℝ} (h : cell872.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell872 residualNumerator check872 h
def RawShard0052Cells : List Cell := [cell875, cell874, cell873, cell872]
theorem RawShard0052Valid : ValidCells RawShard0052Cells := by
  intro c hc x y h
  simp only [RawShard0052Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h875 | h874 | h873 | h872
  · subst c
    exact bound875 h
  · subst c
    exact bound874 h
  · subst c
    exact bound873 h
  · subst c
    exact bound872 h
#print axioms RawShard0052Valid
end PinnCertFarm
