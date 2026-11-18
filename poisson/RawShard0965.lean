import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3783 : Cell := gridCell 256 125 255
theorem check3783 : PinnStaged.check cell3783 = true := by
  decide +kernel
theorem bound3783 {x y : ℝ} (h : cell3783.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3783 check3783 h
def cell3782 : Cell := gridCell 128 63 126
theorem check3782 : PinnStaged.check cell3782 = true := by
  decide +kernel
theorem bound3782 {x y : ℝ} (h : cell3782.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3782 check3782 h
def cell3781 : Cell := gridCell 256 126 254
theorem check3781 : PinnStaged.check cell3781 = true := by
  decide +kernel
theorem bound3781 {x y : ℝ} (h : cell3781.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3781 check3781 h
def cell3780 : Cell := gridCell 256 126 255
theorem check3780 : PinnStaged.check cell3780 = true := by
  decide +kernel
theorem bound3780 {x y : ℝ} (h : cell3780.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3780 check3780 h
def RawShard0965Cells : List Cell := [cell3783, cell3782, cell3781, cell3780]
theorem RawShard0965Valid : ValidCells RawShard0965Cells := by
  intro c hc x y h
  simp only [RawShard0965Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3783 | h3782 | h3781 | h3780
  · subst c
    exact bound3783 h
  · subst c
    exact bound3782 h
  · subst c
    exact bound3781 h
  · subst c
    exact bound3780 h
#print axioms RawShard0965Valid
end PinnCertFarm
