import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6438 : Cell := gridCell 128 96 91
theorem check6438 : PinnStaged.check cell6438 = true := by
  decide +kernel
theorem bound6438 {x y : ℝ} (h : cell6438.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6438 check6438 h
def cell6437 : Cell := gridCell 128 97 90
theorem check6437 : PinnStaged.check cell6437 = true := by
  decide +kernel
theorem bound6437 {x y : ℝ} (h : cell6437.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6437 check6437 h
def cell6436 : Cell := gridCell 128 97 91
theorem check6436 : PinnStaged.check cell6436 = true := by
  decide +kernel
theorem bound6436 {x y : ℝ} (h : cell6436.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6436 check6436 h
def cell6435 : Cell := gridCell 128 98 88
theorem check6435 : PinnStaged.check cell6435 = true := by
  decide +kernel
theorem bound6435 {x y : ℝ} (h : cell6435.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6435 check6435 h
def RawShard1860Cells : List Cell := [cell6438, cell6437, cell6436, cell6435]
theorem RawShard1860Valid : ValidCells RawShard1860Cells := by
  intro c hc x y h
  simp only [RawShard1860Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6438 | h6437 | h6436 | h6435
  · subst c
    exact bound6438 h
  · subst c
    exact bound6437 h
  · subst c
    exact bound6436 h
  · subst c
    exact bound6435 h
#print axioms RawShard1860Valid
end PinnCertFarm
