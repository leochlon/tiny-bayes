import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4127 : Cell := gridCell 128 64 93
theorem check4127 : PinnStaged.check cell4127 = true := by
  decide +kernel
theorem bound4127 {x y : ℝ} (h : cell4127.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4127 check4127 h
def cell4126 : Cell := gridCell 128 65 92
theorem check4126 : PinnStaged.check cell4126 = true := by
  decide +kernel
theorem bound4126 {x y : ℝ} (h : cell4126.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4126 check4126 h
def cell4125 : Cell := gridCell 128 65 93
theorem check4125 : PinnStaged.check cell4125 = true := by
  decide +kernel
theorem bound4125 {x y : ℝ} (h : cell4125.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4125 check4125 h
def cell4124 : Cell := gridCell 64 32 47
theorem check4124 : PinnStaged.check cell4124 = true := by
  decide +kernel
theorem bound4124 {x y : ℝ} (h : cell4124.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4124 check4124 h
def RawShard1399Cells : List Cell := [cell4127, cell4126, cell4125, cell4124]
theorem RawShard1399Valid : ValidCells RawShard1399Cells := by
  intro c hc x y h
  simp only [RawShard1399Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4127 | h4126 | h4125 | h4124
  · subst c
    exact bound4127 h
  · subst c
    exact bound4126 h
  · subst c
    exact bound4125 h
  · subst c
    exact bound4124 h
#print axioms RawShard1399Valid
end PinnCertFarm
