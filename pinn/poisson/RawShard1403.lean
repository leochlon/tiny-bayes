import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4111 : Cell := gridCell 128 69 91
theorem check4111 : PinnStaged.check cell4111 = true := by
  decide +kernel
theorem bound4111 {x y : ℝ} (h : cell4111.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4111 check4111 h
def cell4110 : Cell := gridCell 128 70 88
theorem check4110 : PinnStaged.check cell4110 = true := by
  decide +kernel
theorem bound4110 {x y : ℝ} (h : cell4110.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4110 check4110 h
def cell4109 : Cell := gridCell 128 70 89
theorem check4109 : PinnStaged.check cell4109 = true := by
  decide +kernel
theorem bound4109 {x y : ℝ} (h : cell4109.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4109 check4109 h
def cell4108 : Cell := gridCell 128 71 88
theorem check4108 : PinnStaged.check cell4108 = true := by
  decide +kernel
theorem bound4108 {x y : ℝ} (h : cell4108.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4108 check4108 h
def RawShard1403Cells : List Cell := [cell4111, cell4110, cell4109, cell4108]
theorem RawShard1403Valid : ValidCells RawShard1403Cells := by
  intro c hc x y h
  simp only [RawShard1403Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4111 | h4110 | h4109 | h4108
  · subst c
    exact bound4111 h
  · subst c
    exact bound4110 h
  · subst c
    exact bound4109 h
  · subst c
    exact bound4108 h
#print axioms RawShard1403Valid
end PinnCertFarm
