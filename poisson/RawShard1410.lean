import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4642 : Cell := gridCell 128 73 82
theorem check4642 : PinnStaged.check cell4642 = true := by
  decide +kernel
theorem bound4642 {x y : ℝ} (h : cell4642.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4642 check4642 h
def cell4641 : Cell := gridCell 128 73 83
theorem check4641 : PinnStaged.check cell4641 = true := by
  decide +kernel
theorem bound4641 {x y : ℝ} (h : cell4641.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4641 check4641 h
def cell4640 : Cell := gridCell 128 74 80
theorem check4640 : PinnStaged.check cell4640 = true := by
  decide +kernel
theorem bound4640 {x y : ℝ} (h : cell4640.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4640 check4640 h
def cell4639 : Cell := gridCell 128 74 81
theorem check4639 : PinnStaged.check cell4639 = true := by
  decide +kernel
theorem bound4639 {x y : ℝ} (h : cell4639.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4639 check4639 h
def RawShard1410Cells : List Cell := [cell4642, cell4641, cell4640, cell4639]
theorem RawShard1410Valid : ValidCells RawShard1410Cells := by
  intro c hc x y h
  simp only [RawShard1410Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4642 | h4641 | h4640 | h4639
  · subst c
    exact bound4642 h
  · subst c
    exact bound4641 h
  · subst c
    exact bound4640 h
  · subst c
    exact bound4639 h
#print axioms RawShard1410Valid
end PinnCertFarm
