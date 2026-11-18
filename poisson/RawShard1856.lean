import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6326 : Cell := gridCell 128 100 87
theorem check6326 : PinnStaged.check cell6326 = true := by
  decide +kernel
theorem bound6326 {x y : ℝ} (h : cell6326.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6326 check6326 h
def cell6325 : Cell := gridCell 128 101 86
theorem check6325 : PinnStaged.check cell6325 = true := by
  decide +kernel
theorem bound6325 {x y : ℝ} (h : cell6325.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6325 check6325 h
def cell6324 : Cell := gridCell 128 101 87
theorem check6324 : PinnStaged.check cell6324 = true := by
  decide +kernel
theorem bound6324 {x y : ℝ} (h : cell6324.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6324 check6324 h
def cell6323 : Cell := gridCell 128 102 84
theorem check6323 : PinnStaged.check cell6323 = true := by
  decide +kernel
theorem bound6323 {x y : ℝ} (h : cell6323.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6323 check6323 h
def RawShard1856Cells : List Cell := [cell6326, cell6325, cell6324, cell6323]
theorem RawShard1856Valid : ValidCells RawShard1856Cells := by
  intro c hc x y h
  simp only [RawShard1856Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6326 | h6325 | h6324 | h6323
  · subst c
    exact bound6326 h
  · subst c
    exact bound6325 h
  · subst c
    exact bound6324 h
  · subst c
    exact bound6323 h
#print axioms RawShard1856Valid
end PinnCertFarm
