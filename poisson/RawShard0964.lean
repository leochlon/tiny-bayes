import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3787 : Cell := gridCell 128 62 126
theorem check3787 : PinnStaged.check cell3787 = true := by
  decide +kernel
theorem bound3787 {x y : ℝ} (h : cell3787.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3787 check3787 h
def cell3786 : Cell := gridCell 256 124 254
theorem check3786 : PinnStaged.check cell3786 = true := by
  decide +kernel
theorem bound3786 {x y : ℝ} (h : cell3786.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3786 check3786 h
def cell3785 : Cell := gridCell 256 124 255
theorem check3785 : PinnStaged.check cell3785 = true := by
  decide +kernel
theorem bound3785 {x y : ℝ} (h : cell3785.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3785 check3785 h
def cell3784 : Cell := gridCell 256 125 254
theorem check3784 : PinnStaged.check cell3784 = true := by
  decide +kernel
theorem bound3784 {x y : ℝ} (h : cell3784.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3784 check3784 h
def RawShard0964Cells : List Cell := [cell3787, cell3786, cell3785, cell3784]
theorem RawShard0964Valid : ValidCells RawShard0964Cells := by
  intro c hc x y h
  simp only [RawShard0964Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3787 | h3786 | h3785 | h3784
  · subst c
    exact bound3787 h
  · subst c
    exact bound3786 h
  · subst c
    exact bound3785 h
  · subst c
    exact bound3784 h
#print axioms RawShard0964Valid
end PinnCertFarm
