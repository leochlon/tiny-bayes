import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4095 : Cell := gridCell 128 71 92
theorem check4095 : PinnStaged.check cell4095 = true := by
  decide +kernel
theorem bound4095 {x y : ℝ} (h : cell4095.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4095 check4095 h
def cell4094 : Cell := gridCell 128 71 93
theorem check4094 : PinnStaged.check cell4094 = true := by
  decide +kernel
theorem bound4094 {x y : ℝ} (h : cell4094.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4094 check4094 h
def cell4093 : Cell := gridCell 128 70 94
theorem check4093 : PinnStaged.check cell4093 = true := by
  decide +kernel
theorem bound4093 {x y : ℝ} (h : cell4093.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4093 check4093 h
def cell4092 : Cell := gridCell 128 70 95
theorem check4092 : PinnStaged.check cell4092 = true := by
  decide +kernel
theorem bound4092 {x y : ℝ} (h : cell4092.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4092 check4092 h
def RawShard1407Cells : List Cell := [cell4095, cell4094, cell4093, cell4092]
theorem RawShard1407Valid : ValidCells RawShard1407Cells := by
  intro c hc x y h
  simp only [RawShard1407Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4095 | h4094 | h4093 | h4092
  · subst c
    exact bound4095 h
  · subst c
    exact bound4094 h
  · subst c
    exact bound4093 h
  · subst c
    exact bound4092 h
#print axioms RawShard1407Valid
end PinnCertFarm
