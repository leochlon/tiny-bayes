import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3807 : Cell := gridCell 128 63 122
theorem check3807 : PinnStaged.check cell3807 = true := by
  decide +kernel
theorem bound3807 {x y : ℝ} (h : cell3807.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3807 check3807 h
def cell3806 : Cell := gridCell 128 63 123
theorem check3806 : PinnStaged.check cell3806 = true := by
  decide +kernel
theorem bound3806 {x y : ℝ} (h : cell3806.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3806 check3806 h
def cell3805 : Cell := gridCell 128 60 124
theorem check3805 : PinnStaged.check cell3805 = true := by
  decide +kernel
theorem bound3805 {x y : ℝ} (h : cell3805.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3805 check3805 h
def cell3804 : Cell := gridCell 128 60 125
theorem check3804 : PinnStaged.check cell3804 = true := by
  decide +kernel
theorem bound3804 {x y : ℝ} (h : cell3804.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3804 check3804 h
def RawShard0959Cells : List Cell := [cell3807, cell3806, cell3805, cell3804]
theorem RawShard0959Valid : ValidCells RawShard0959Cells := by
  intro c hc x y h
  simp only [RawShard0959Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3807 | h3806 | h3805 | h3804
  · subst c
    exact bound3807 h
  · subst c
    exact bound3806 h
  · subst c
    exact bound3805 h
  · subst c
    exact bound3804 h
#print axioms RawShard0959Valid
end PinnCertFarm
