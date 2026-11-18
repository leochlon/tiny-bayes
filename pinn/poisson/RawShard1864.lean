import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6422 : Cell := gridCell 128 96 95
theorem check6422 : PinnStaged.check cell6422 = true := by
  decide +kernel
theorem bound6422 {x y : ℝ} (h : cell6422.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6422 check6422 h
def cell6421 : Cell := gridCell 128 97 94
theorem check6421 : PinnStaged.check cell6421 = true := by
  decide +kernel
theorem bound6421 {x y : ℝ} (h : cell6421.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6421 check6421 h
def cell6420 : Cell := gridCell 128 97 95
theorem check6420 : PinnStaged.check cell6420 = true := by
  decide +kernel
theorem bound6420 {x y : ℝ} (h : cell6420.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6420 check6420 h
def cell6419 : Cell := gridCell 128 98 92
theorem check6419 : PinnStaged.check cell6419 = true := by
  decide +kernel
theorem bound6419 {x y : ℝ} (h : cell6419.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6419 check6419 h
def RawShard1864Cells : List Cell := [cell6422, cell6421, cell6420, cell6419]
theorem RawShard1864Valid : ValidCells RawShard1864Cells := by
  intro c hc x y h
  simp only [RawShard1864Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6422 | h6421 | h6420 | h6419
  · subst c
    exact bound6422 h
  · subst c
    exact bound6421 h
  · subst c
    exact bound6420 h
  · subst c
    exact bound6419 h
#print axioms RawShard1864Valid
end PinnCertFarm
