import FarmSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell39 : Cell := gridCell 64 2 8
theorem check39 : Cell.secondCheck normalizedResidual cell39 residualNumerator = true := by
  decide +kernel
theorem bound39 {x y : ℝ} (h : cell39.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell39 residualNumerator check39 h
def cell38 : Cell := gridCell 64 2 9
theorem check38 : Cell.secondCheck normalizedResidual cell38 residualNumerator = true := by
  decide +kernel
theorem bound38 {x y : ℝ} (h : cell38.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell38 residualNumerator check38 h
def cell37 : Cell := gridCell 64 3 8
theorem check37 : Cell.secondCheck normalizedResidual cell37 residualNumerator = true := by
  decide +kernel
theorem bound37 {x y : ℝ} (h : cell37.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell37 residualNumerator check37 h
def cell36 : Cell := gridCell 64 3 9
theorem check36 : Cell.secondCheck normalizedResidual cell36 residualNumerator = true := by
  decide +kernel
theorem bound36 {x y : ℝ} (h : cell36.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondCheck_sound normalizedResidual cell36 residualNumerator check36 h
def RawShard0018Cells : List Cell := [cell39, cell38, cell37, cell36]
theorem RawShard0018Valid : ValidCells RawShard0018Cells := by
  intro c hc x y h
  simp only [RawShard0018Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h39 | h38 | h37 | h36
  · subst c
    exact bound39 h
  · subst c
    exact bound38 h
  · subst c
    exact bound37 h
  · subst c
    exact bound36 h
#print axioms RawShard0018Valid
end PinnCertFarm
