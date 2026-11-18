import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6414 : Cell := gridCell 128 98 95
theorem check6414 : PinnStaged.check cell6414 = true := by
  decide +kernel
theorem bound6414 {x y : ℝ} (h : cell6414.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6414 check6414 h
def cell6413 : Cell := gridCell 128 99 94
theorem check6413 : PinnStaged.check cell6413 = true := by
  decide +kernel
theorem bound6413 {x y : ℝ} (h : cell6413.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6413 check6413 h
def cell6412 : Cell := gridCell 128 99 95
theorem check6412 : PinnStaged.check cell6412 = true := by
  decide +kernel
theorem bound6412 {x y : ℝ} (h : cell6412.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6412 check6412 h
def cell6411 : Cell := gridCell 128 100 88
theorem check6411 : PinnStaged.check cell6411 = true := by
  decide +kernel
theorem bound6411 {x y : ℝ} (h : cell6411.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6411 check6411 h
def RawShard1866Cells : List Cell := [cell6414, cell6413, cell6412, cell6411]
theorem RawShard1866Valid : ValidCells RawShard1866Cells := by
  intro c hc x y h
  simp only [RawShard1866Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6414 | h6413 | h6412 | h6411
  · subst c
    exact bound6414 h
  · subst c
    exact bound6413 h
  · subst c
    exact bound6412 h
  · subst c
    exact bound6411 h
#print axioms RawShard1866Valid
end PinnCertFarm
