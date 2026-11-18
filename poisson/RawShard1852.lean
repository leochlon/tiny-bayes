import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6342 : Cell := gridCell 128 100 83
theorem check6342 : PinnStaged.check cell6342 = true := by
  decide +kernel
theorem bound6342 {x y : ℝ} (h : cell6342.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6342 check6342 h
def cell6341 : Cell := gridCell 128 101 82
theorem check6341 : PinnStaged.check cell6341 = true := by
  decide +kernel
theorem bound6341 {x y : ℝ} (h : cell6341.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6341 check6341 h
def cell6340 : Cell := gridCell 128 101 83
theorem check6340 : PinnStaged.check cell6340 = true := by
  decide +kernel
theorem bound6340 {x y : ℝ} (h : cell6340.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6340 check6340 h
def cell6339 : Cell := gridCell 128 102 80
theorem check6339 : PinnStaged.check cell6339 = true := by
  decide +kernel
theorem bound6339 {x y : ℝ} (h : cell6339.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6339 check6339 h
def RawShard1852Cells : List Cell := [cell6342, cell6341, cell6340, cell6339]
theorem RawShard1852Valid : ValidCells RawShard1852Cells := by
  intro c hc x y h
  simp only [RawShard1852Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6342 | h6341 | h6340 | h6339
  · subst c
    exact bound6342 h
  · subst c
    exact bound6341 h
  · subst c
    exact bound6340 h
  · subst c
    exact bound6339 h
#print axioms RawShard1852Valid
end PinnCertFarm
