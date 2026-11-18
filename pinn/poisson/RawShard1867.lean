import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6410 : Cell := gridCell 128 100 89
theorem check6410 : PinnStaged.check cell6410 = true := by
  decide +kernel
theorem bound6410 {x y : ℝ} (h : cell6410.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6410 check6410 h
def cell6409 : Cell := gridCell 128 101 88
theorem check6409 : PinnStaged.check cell6409 = true := by
  decide +kernel
theorem bound6409 {x y : ℝ} (h : cell6409.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6409 check6409 h
def cell6408 : Cell := gridCell 128 101 89
theorem check6408 : PinnStaged.check cell6408 = true := by
  decide +kernel
theorem bound6408 {x y : ℝ} (h : cell6408.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6408 check6408 h
def cell6407 : Cell := gridCell 128 100 90
theorem check6407 : PinnStaged.check cell6407 = true := by
  decide +kernel
theorem bound6407 {x y : ℝ} (h : cell6407.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6407 check6407 h
def RawShard1867Cells : List Cell := [cell6410, cell6409, cell6408, cell6407]
theorem RawShard1867Valid : ValidCells RawShard1867Cells := by
  intro c hc x y h
  simp only [RawShard1867Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6410 | h6409 | h6408 | h6407
  · subst c
    exact bound6410 h
  · subst c
    exact bound6409 h
  · subst c
    exact bound6408 h
  · subst c
    exact bound6407 h
#print axioms RawShard1867Valid
end PinnCertFarm
