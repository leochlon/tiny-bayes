import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4602 : Cell := gridCell 128 79 82
theorem check4602 : PinnStaged.check cell4602 = true := by
  decide +kernel
theorem bound4602 {x y : ℝ} (h : cell4602.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4602 check4602 h
def cell4601 : Cell := gridCell 128 79 83
theorem check4601 : PinnStaged.check cell4601 = true := by
  decide +kernel
theorem bound4601 {x y : ℝ} (h : cell4601.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4601 check4601 h
def cell4600 : Cell := gridCell 128 76 84
theorem check4600 : PinnStaged.check cell4600 = true := by
  decide +kernel
theorem bound4600 {x y : ℝ} (h : cell4600.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4600 check4600 h
def cell4599 : Cell := gridCell 128 76 85
theorem check4599 : PinnStaged.check cell4599 = true := by
  decide +kernel
theorem bound4599 {x y : ℝ} (h : cell4599.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4599 check4599 h
def RawShard1420Cells : List Cell := [cell4602, cell4601, cell4600, cell4599]
theorem RawShard1420Valid : ValidCells RawShard1420Cells := by
  intro c hc x y h
  simp only [RawShard1420Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4602 | h4601 | h4600 | h4599
  · subst c
    exact bound4602 h
  · subst c
    exact bound4601 h
  · subst c
    exact bound4600 h
  · subst c
    exact bound4599 h
#print axioms RawShard1420Valid
end PinnCertFarm
