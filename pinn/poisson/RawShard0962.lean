import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3795 : Cell := gridCell 256 122 254
theorem check3795 : PinnStaged.check cell3795 = true := by
  decide +kernel
theorem bound3795 {x y : ℝ} (h : cell3795.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3795 check3795 h
def cell3794 : Cell := gridCell 256 122 255
theorem check3794 : PinnStaged.check cell3794 = true := by
  decide +kernel
theorem bound3794 {x y : ℝ} (h : cell3794.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3794 check3794 h
def cell3793 : Cell := gridCell 256 123 254
theorem check3793 : PinnStaged.check cell3793 = true := by
  decide +kernel
theorem bound3793 {x y : ℝ} (h : cell3793.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3793 check3793 h
def cell3792 : Cell := gridCell 256 123 255
theorem check3792 : PinnStaged.check cell3792 = true := by
  decide +kernel
theorem bound3792 {x y : ℝ} (h : cell3792.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3792 check3792 h
def RawShard0962Cells : List Cell := [cell3795, cell3794, cell3793, cell3792]
theorem RawShard0962Valid : ValidCells RawShard0962Cells := by
  intro c hc x y h
  simp only [RawShard0962Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3795 | h3794 | h3793 | h3792
  · subst c
    exact bound3795 h
  · subst c
    exact bound3794 h
  · subst c
    exact bound3793 h
  · subst c
    exact bound3792 h
#print axioms RawShard0962Valid
end PinnCertFarm
