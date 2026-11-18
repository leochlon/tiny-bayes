import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3835 : Cell := gridCell 128 58 124
theorem check3835 : PinnStaged.check cell3835 = true := by
  decide +kernel
theorem bound3835 {x y : ℝ} (h : cell3835.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3835 check3835 h
def cell3834 : Cell := gridCell 128 58 125
theorem check3834 : PinnStaged.check cell3834 = true := by
  decide +kernel
theorem bound3834 {x y : ℝ} (h : cell3834.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3834 check3834 h
def cell3833 : Cell := gridCell 128 59 124
theorem check3833 : PinnStaged.check cell3833 = true := by
  decide +kernel
theorem bound3833 {x y : ℝ} (h : cell3833.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3833 check3833 h
def cell3832 : Cell := gridCell 128 59 125
theorem check3832 : PinnStaged.check cell3832 = true := by
  decide +kernel
theorem bound3832 {x y : ℝ} (h : cell3832.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3832 check3832 h
def RawShard0952Cells : List Cell := [cell3835, cell3834, cell3833, cell3832]
theorem RawShard0952Valid : ValidCells RawShard0952Cells := by
  intro c hc x y h
  simp only [RawShard0952Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3835 | h3834 | h3833 | h3832
  · subst c
    exact bound3835 h
  · subst c
    exact bound3834 h
  · subst c
    exact bound3833 h
  · subst c
    exact bound3832 h
#print axioms RawShard0952Valid
end PinnCertFarm
