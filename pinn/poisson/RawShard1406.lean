import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4099 : Cell := gridCell 128 69 93
theorem check4099 : PinnStaged.check cell4099 = true := by
  decide +kernel
theorem bound4099 {x y : ℝ} (h : cell4099.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4099 check4099 h
def cell4098 : Cell := gridCell 64 34 47
theorem check4098 : PinnStaged.check cell4098 = true := by
  decide +kernel
theorem bound4098 {x y : ℝ} (h : cell4098.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4098 check4098 h
def cell4097 : Cell := gridCell 128 70 92
theorem check4097 : PinnStaged.check cell4097 = true := by
  decide +kernel
theorem bound4097 {x y : ℝ} (h : cell4097.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4097 check4097 h
def cell4096 : Cell := gridCell 128 70 93
theorem check4096 : PinnStaged.check cell4096 = true := by
  decide +kernel
theorem bound4096 {x y : ℝ} (h : cell4096.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4096 check4096 h
def RawShard1406Cells : List Cell := [cell4099, cell4098, cell4097, cell4096]
theorem RawShard1406Valid : ValidCells RawShard1406Cells := by
  intro c hc x y h
  simp only [RawShard1406Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4099 | h4098 | h4097 | h4096
  · subst c
    exact bound4099 h
  · subst c
    exact bound4098 h
  · subst c
    exact bound4097 h
  · subst c
    exact bound4096 h
#print axioms RawShard1406Valid
end PinnCertFarm
