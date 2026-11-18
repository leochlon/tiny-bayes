import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3831 : Cell := gridCell 128 58 126
theorem check3831 : PinnStaged.check cell3831 = true := by
  decide +kernel
theorem bound3831 {x y : ℝ} (h : cell3831.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3831 check3831 h
def cell3830 : Cell := gridCell 256 116 254
theorem check3830 : PinnStaged.check cell3830 = true := by
  decide +kernel
theorem bound3830 {x y : ℝ} (h : cell3830.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3830 check3830 h
def cell3829 : Cell := gridCell 256 116 255
theorem check3829 : PinnStaged.check cell3829 = true := by
  decide +kernel
theorem bound3829 {x y : ℝ} (h : cell3829.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3829 check3829 h
def cell3828 : Cell := gridCell 256 117 254
theorem check3828 : PinnStaged.check cell3828 = true := by
  decide +kernel
theorem bound3828 {x y : ℝ} (h : cell3828.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3828 check3828 h
def RawShard0953Cells : List Cell := [cell3831, cell3830, cell3829, cell3828]
theorem RawShard0953Valid : ValidCells RawShard0953Cells := by
  intro c hc x y h
  simp only [RawShard0953Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3831 | h3830 | h3829 | h3828
  · subst c
    exact bound3831 h
  · subst c
    exact bound3830 h
  · subst c
    exact bound3829 h
  · subst c
    exact bound3828 h
#print axioms RawShard0953Valid
end PinnCertFarm
