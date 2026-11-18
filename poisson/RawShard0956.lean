import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3819 : Cell := gridCell 128 61 120
theorem check3819 : PinnStaged.check cell3819 = true := by
  decide +kernel
theorem bound3819 {x y : ℝ} (h : cell3819.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3819 check3819 h
def cell3818 : Cell := gridCell 128 61 121
theorem check3818 : PinnStaged.check cell3818 = true := by
  decide +kernel
theorem bound3818 {x y : ℝ} (h : cell3818.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3818 check3818 h
def cell3817 : Cell := gridCell 128 60 122
theorem check3817 : PinnStaged.check cell3817 = true := by
  decide +kernel
theorem bound3817 {x y : ℝ} (h : cell3817.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3817 check3817 h
def cell3816 : Cell := gridCell 128 60 123
theorem check3816 : PinnStaged.check cell3816 = true := by
  decide +kernel
theorem bound3816 {x y : ℝ} (h : cell3816.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3816 check3816 h
def RawShard0956Cells : List Cell := [cell3819, cell3818, cell3817, cell3816]
theorem RawShard0956Valid : ValidCells RawShard0956Cells := by
  intro c hc x y h
  simp only [RawShard0956Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3819 | h3818 | h3817 | h3816
  · subst c
    exact bound3819 h
  · subst c
    exact bound3818 h
  · subst c
    exact bound3817 h
  · subst c
    exact bound3816 h
#print axioms RawShard0956Valid
end PinnCertFarm
