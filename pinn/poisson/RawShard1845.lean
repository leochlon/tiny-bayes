import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6370 : Cell := gridCell 128 98 81
theorem check6370 : PinnStaged.check cell6370 = true := by
  decide +kernel
theorem bound6370 {x y : ℝ} (h : cell6370.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6370 check6370 h
def cell6369 : Cell := gridCell 128 99 80
theorem check6369 : PinnStaged.check cell6369 = true := by
  decide +kernel
theorem bound6369 {x y : ℝ} (h : cell6369.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6369 check6369 h
def cell6368 : Cell := gridCell 128 99 81
theorem check6368 : PinnStaged.check cell6368 = true := by
  decide +kernel
theorem bound6368 {x y : ℝ} (h : cell6368.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6368 check6368 h
def cell6367 : Cell := gridCell 128 98 82
theorem check6367 : PinnStaged.check cell6367 = true := by
  decide +kernel
theorem bound6367 {x y : ℝ} (h : cell6367.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6367 check6367 h
def RawShard1845Cells : List Cell := [cell6370, cell6369, cell6368, cell6367]
theorem RawShard1845Valid : ValidCells RawShard1845Cells := by
  intro c hc x y h
  simp only [RawShard1845Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6370 | h6369 | h6368 | h6367
  · subst c
    exact bound6370 h
  · subst c
    exact bound6369 h
  · subst c
    exact bound6368 h
  · subst c
    exact bound6367 h
#print axioms RawShard1845Valid
end PinnCertFarm
