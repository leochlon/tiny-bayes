import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4634 : Cell := gridCell 128 75 82
theorem check4634 : PinnStaged.check cell4634 = true := by
  decide +kernel
theorem bound4634 {x y : ℝ} (h : cell4634.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4634 check4634 h
def cell4633 : Cell := gridCell 128 75 83
theorem check4633 : PinnStaged.check cell4633 = true := by
  decide +kernel
theorem bound4633 {x y : ℝ} (h : cell4633.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4633 check4633 h
def cell4632 : Cell := gridCell 128 72 84
theorem check4632 : PinnStaged.check cell4632 = true := by
  decide +kernel
theorem bound4632 {x y : ℝ} (h : cell4632.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4632 check4632 h
def cell4631 : Cell := gridCell 128 72 85
theorem check4631 : PinnStaged.check cell4631 = true := by
  decide +kernel
theorem bound4631 {x y : ℝ} (h : cell4631.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4631 check4631 h
def RawShard1412Cells : List Cell := [cell4634, cell4633, cell4632, cell4631]
theorem RawShard1412Valid : ValidCells RawShard1412Cells := by
  intro c hc x y h
  simp only [RawShard1412Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4634 | h4633 | h4632 | h4631
  · subst c
    exact bound4634 h
  · subst c
    exact bound4633 h
  · subst c
    exact bound4632 h
  · subst c
    exact bound4631 h
#print axioms RawShard1412Valid
end PinnCertFarm
