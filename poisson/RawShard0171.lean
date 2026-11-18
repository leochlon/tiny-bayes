import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3316 : Cell := gridCell 64 30 2
theorem check3316 : PinnStaged.check cell3316 = true := by
  decide +kernel
theorem bound3316 {x y : ℝ} (h : cell3316.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3316 check3316 h
def cell3315 : Cell := gridCell 64 30 3
theorem check3315 : PinnStaged.check cell3315 = true := by
  decide +kernel
theorem bound3315 {x y : ℝ} (h : cell3315.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3315 check3315 h
def cell3314 : Cell := gridCell 64 31 2
theorem check3314 : PinnStaged.check cell3314 = true := by
  decide +kernel
theorem bound3314 {x y : ℝ} (h : cell3314.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3314 check3314 h
def cell3313 : Cell := gridCell 64 31 3
theorem check3313 : PinnStaged.check cell3313 = true := by
  decide +kernel
theorem bound3313 {x y : ℝ} (h : cell3313.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3313 check3313 h
def RawShard0171Cells : List Cell := [cell3316, cell3315, cell3314, cell3313]
theorem RawShard0171Valid : ValidCells RawShard0171Cells := by
  intro c hc x y h
  simp only [RawShard0171Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3316 | h3315 | h3314 | h3313
  · subst c
    exact bound3316 h
  · subst c
    exact bound3315 h
  · subst c
    exact bound3314 h
  · subst c
    exact bound3313 h
#print axioms RawShard0171Valid
end PinnCertFarm
