import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4107 : Cell := gridCell 128 71 89
theorem check4107 : PinnStaged.check cell4107 = true := by
  decide +kernel
theorem bound4107 {x y : ℝ} (h : cell4107.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4107 check4107 h
def cell4106 : Cell := gridCell 128 70 90
theorem check4106 : PinnStaged.check cell4106 = true := by
  decide +kernel
theorem bound4106 {x y : ℝ} (h : cell4106.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4106 check4106 h
def cell4105 : Cell := gridCell 128 70 91
theorem check4105 : PinnStaged.check cell4105 = true := by
  decide +kernel
theorem bound4105 {x y : ℝ} (h : cell4105.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4105 check4105 h
def cell4104 : Cell := gridCell 128 71 90
theorem check4104 : PinnStaged.check cell4104 = true := by
  decide +kernel
theorem bound4104 {x y : ℝ} (h : cell4104.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4104 check4104 h
def RawShard1404Cells : List Cell := [cell4107, cell4106, cell4105, cell4104]
theorem RawShard1404Valid : ValidCells RawShard1404Cells := by
  intro c hc x y h
  simp only [RawShard1404Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4107 | h4106 | h4105 | h4104
  · subst c
    exact bound4107 h
  · subst c
    exact bound4106 h
  · subst c
    exact bound4105 h
  · subst c
    exact bound4104 h
#print axioms RawShard1404Valid
end PinnCertFarm
