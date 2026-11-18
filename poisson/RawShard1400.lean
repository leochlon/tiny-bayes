import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4123 : Cell := gridCell 128 66 92
theorem check4123 : PinnStaged.check cell4123 = true := by
  decide +kernel
theorem bound4123 {x y : ℝ} (h : cell4123.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4123 check4123 h
def cell4122 : Cell := gridCell 128 66 93
theorem check4122 : PinnStaged.check cell4122 = true := by
  decide +kernel
theorem bound4122 {x y : ℝ} (h : cell4122.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4122 check4122 h
def cell4121 : Cell := gridCell 128 67 92
theorem check4121 : PinnStaged.check cell4121 = true := by
  decide +kernel
theorem bound4121 {x y : ℝ} (h : cell4121.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4121 check4121 h
def cell4120 : Cell := gridCell 128 67 93
theorem check4120 : PinnStaged.check cell4120 = true := by
  decide +kernel
theorem bound4120 {x y : ℝ} (h : cell4120.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4120 check4120 h
def RawShard1400Cells : List Cell := [cell4123, cell4122, cell4121, cell4120]
theorem RawShard1400Valid : ValidCells RawShard1400Cells := by
  intro c hc x y h
  simp only [RawShard1400Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4123 | h4122 | h4121 | h4120
  · subst c
    exact bound4123 h
  · subst c
    exact bound4122 h
  · subst c
    exact bound4121 h
  · subst c
    exact bound4120 h
#print axioms RawShard1400Valid
end PinnCertFarm
