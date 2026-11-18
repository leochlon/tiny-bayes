import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3360 : Cell := gridCell 64 28 8
theorem check3360 : PinnStaged.check cell3360 = true := by
  decide +kernel
theorem bound3360 {x y : ℝ} (h : cell3360.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3360 check3360 h
def cell3359 : Cell := gridCell 64 28 9
theorem check3359 : PinnStaged.check cell3359 = true := by
  decide +kernel
theorem bound3359 {x y : ℝ} (h : cell3359.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3359 check3359 h
def cell3358 : Cell := gridCell 64 29 8
theorem check3358 : PinnStaged.check cell3358 = true := by
  decide +kernel
theorem bound3358 {x y : ℝ} (h : cell3358.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3358 check3358 h
def cell3357 : Cell := gridCell 64 29 9
theorem check3357 : PinnStaged.check cell3357 = true := by
  decide +kernel
theorem bound3357 {x y : ℝ} (h : cell3357.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3357 check3357 h
def RawShard0184Cells : List Cell := [cell3360, cell3359, cell3358, cell3357]
theorem RawShard0184Valid : ValidCells RawShard0184Cells := by
  intro c hc x y h
  simp only [RawShard0184Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3360 | h3359 | h3358 | h3357
  · subst c
    exact bound3360 h
  · subst c
    exact bound3359 h
  · subst c
    exact bound3358 h
  · subst c
    exact bound3357 h
#print axioms RawShard0184Valid
end PinnCertFarm
