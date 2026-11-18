import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3328 : Cell := gridCell 64 28 0
theorem check3328 : PinnStaged.check cell3328 = true := by
  decide +kernel
theorem bound3328 {x y : ℝ} (h : cell3328.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3328 check3328 h
def cell3327 : Cell := gridCell 64 28 1
theorem check3327 : PinnStaged.check cell3327 = true := by
  decide +kernel
theorem bound3327 {x y : ℝ} (h : cell3327.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3327 check3327 h
def cell3326 : Cell := gridCell 64 29 0
theorem check3326 : PinnStaged.check cell3326 = true := by
  decide +kernel
theorem bound3326 {x y : ℝ} (h : cell3326.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3326 check3326 h
def cell3325 : Cell := gridCell 64 29 1
theorem check3325 : PinnStaged.check cell3325 = true := by
  decide +kernel
theorem bound3325 {x y : ℝ} (h : cell3325.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3325 check3325 h
def RawShard0168Cells : List Cell := [cell3328, cell3327, cell3326, cell3325]
theorem RawShard0168Valid : ValidCells RawShard0168Cells := by
  intro c hc x y h
  simp only [RawShard0168Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3328 | h3327 | h3326 | h3325
  · subst c
    exact bound3328 h
  · subst c
    exact bound3327 h
  · subst c
    exact bound3326 h
  · subst c
    exact bound3325 h
#print axioms RawShard0168Valid
end PinnCertFarm
