import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6346 : Cell := gridCell 128 100 81
theorem check6346 : PinnStaged.check cell6346 = true := by
  decide +kernel
theorem bound6346 {x y : ℝ} (h : cell6346.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6346 check6346 h
def cell6345 : Cell := gridCell 128 101 80
theorem check6345 : PinnStaged.check cell6345 = true := by
  decide +kernel
theorem bound6345 {x y : ℝ} (h : cell6345.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6345 check6345 h
def cell6344 : Cell := gridCell 128 101 81
theorem check6344 : PinnStaged.check cell6344 = true := by
  decide +kernel
theorem bound6344 {x y : ℝ} (h : cell6344.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6344 check6344 h
def cell6343 : Cell := gridCell 128 100 82
theorem check6343 : PinnStaged.check cell6343 = true := by
  decide +kernel
theorem bound6343 {x y : ℝ} (h : cell6343.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6343 check6343 h
def RawShard1851Cells : List Cell := [cell6346, cell6345, cell6344, cell6343]
theorem RawShard1851Valid : ValidCells RawShard1851Cells := by
  intro c hc x y h
  simp only [RawShard1851Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6346 | h6345 | h6344 | h6343
  · subst c
    exact bound6346 h
  · subst c
    exact bound6345 h
  · subst c
    exact bound6344 h
  · subst c
    exact bound6343 h
#print axioms RawShard1851Valid
end PinnCertFarm
