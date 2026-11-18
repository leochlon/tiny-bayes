import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3376 : Cell := gridCell 64 28 12
theorem check3376 : PinnStaged.check cell3376 = true := by
  decide +kernel
theorem bound3376 {x y : ℝ} (h : cell3376.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3376 check3376 h
def cell3375 : Cell := gridCell 64 28 13
theorem check3375 : PinnStaged.check cell3375 = true := by
  decide +kernel
theorem bound3375 {x y : ℝ} (h : cell3375.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3375 check3375 h
def cell3374 : Cell := gridCell 64 29 12
theorem check3374 : PinnStaged.check cell3374 = true := by
  decide +kernel
theorem bound3374 {x y : ℝ} (h : cell3374.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3374 check3374 h
def cell3373 : Cell := gridCell 64 29 13
theorem check3373 : PinnStaged.check cell3373 = true := by
  decide +kernel
theorem bound3373 {x y : ℝ} (h : cell3373.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3373 check3373 h
def RawShard0188Cells : List Cell := [cell3376, cell3375, cell3374, cell3373]
theorem RawShard0188Valid : ValidCells RawShard0188Cells := by
  intro c hc x y h
  simp only [RawShard0188Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3376 | h3375 | h3374 | h3373
  · subst c
    exact bound3376 h
  · subst c
    exact bound3375 h
  · subst c
    exact bound3374 h
  · subst c
    exact bound3373 h
#print axioms RawShard0188Valid
end PinnCertFarm
