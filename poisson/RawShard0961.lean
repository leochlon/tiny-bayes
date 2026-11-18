import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3799 : Cell := gridCell 256 120 255
theorem check3799 : PinnStaged.check cell3799 = true := by
  decide +kernel
theorem bound3799 {x y : ℝ} (h : cell3799.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3799 check3799 h
def cell3798 : Cell := gridCell 256 121 254
theorem check3798 : PinnStaged.check cell3798 = true := by
  decide +kernel
theorem bound3798 {x y : ℝ} (h : cell3798.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3798 check3798 h
def cell3797 : Cell := gridCell 256 121 255
theorem check3797 : PinnStaged.check cell3797 = true := by
  decide +kernel
theorem bound3797 {x y : ℝ} (h : cell3797.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3797 check3797 h
def cell3796 : Cell := gridCell 128 61 126
theorem check3796 : PinnStaged.check cell3796 = true := by
  decide +kernel
theorem bound3796 {x y : ℝ} (h : cell3796.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3796 check3796 h
def RawShard0961Cells : List Cell := [cell3799, cell3798, cell3797, cell3796]
theorem RawShard0961Valid : ValidCells RawShard0961Cells := by
  intro c hc x y h
  simp only [RawShard0961Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3799 | h3798 | h3797 | h3796
  · subst c
    exact bound3799 h
  · subst c
    exact bound3798 h
  · subst c
    exact bound3797 h
  · subst c
    exact bound3796 h
#print axioms RawShard0961Valid
end PinnCertFarm
