import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6430 : Cell := gridCell 128 98 91
theorem check6430 : PinnStaged.check cell6430 = true := by
  decide +kernel
theorem bound6430 {x y : ℝ} (h : cell6430.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6430 check6430 h
def cell6429 : Cell := gridCell 128 99 90
theorem check6429 : PinnStaged.check cell6429 = true := by
  decide +kernel
theorem bound6429 {x y : ℝ} (h : cell6429.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6429 check6429 h
def cell6428 : Cell := gridCell 128 99 91
theorem check6428 : PinnStaged.check cell6428 = true := by
  decide +kernel
theorem bound6428 {x y : ℝ} (h : cell6428.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6428 check6428 h
def cell6427 : Cell := gridCell 128 96 92
theorem check6427 : PinnStaged.check cell6427 = true := by
  decide +kernel
theorem bound6427 {x y : ℝ} (h : cell6427.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6427 check6427 h
def RawShard1862Cells : List Cell := [cell6430, cell6429, cell6428, cell6427]
theorem RawShard1862Valid : ValidCells RawShard1862Cells := by
  intro c hc x y h
  simp only [RawShard1862Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6430 | h6429 | h6428 | h6427
  · subst c
    exact bound6430 h
  · subst c
    exact bound6429 h
  · subst c
    exact bound6428 h
  · subst c
    exact bound6427 h
#print axioms RawShard1862Valid
end PinnCertFarm
