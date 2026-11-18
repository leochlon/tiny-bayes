import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3815 : Cell := gridCell 128 61 122
theorem check3815 : PinnStaged.check cell3815 = true := by
  decide +kernel
theorem bound3815 {x y : ℝ} (h : cell3815.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3815 check3815 h
def cell3814 : Cell := gridCell 128 61 123
theorem check3814 : PinnStaged.check cell3814 = true := by
  decide +kernel
theorem bound3814 {x y : ℝ} (h : cell3814.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3814 check3814 h
def cell3813 : Cell := gridCell 128 62 120
theorem check3813 : PinnStaged.check cell3813 = true := by
  decide +kernel
theorem bound3813 {x y : ℝ} (h : cell3813.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3813 check3813 h
def cell3812 : Cell := gridCell 128 62 121
theorem check3812 : PinnStaged.check cell3812 = true := by
  decide +kernel
theorem bound3812 {x y : ℝ} (h : cell3812.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3812 check3812 h
def RawShard0957Cells : List Cell := [cell3815, cell3814, cell3813, cell3812]
theorem RawShard0957Valid : ValidCells RawShard0957Cells := by
  intro c hc x y h
  simp only [RawShard0957Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3815 | h3814 | h3813 | h3812
  · subst c
    exact bound3815 h
  · subst c
    exact bound3814 h
  · subst c
    exact bound3813 h
  · subst c
    exact bound3812 h
#print axioms RawShard0957Valid
end PinnCertFarm
