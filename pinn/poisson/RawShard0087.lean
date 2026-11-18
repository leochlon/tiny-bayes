import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell115 : Cell := gridCell 64 2 30
theorem check115 : PinnStaged.check cell115 = true := by
  decide +kernel
theorem bound115 {x y : ℝ} (h : cell115.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell115 check115 h
def cell114 : Cell := gridCell 64 2 31
theorem check114 : PinnStaged.check cell114 = true := by
  decide +kernel
theorem bound114 {x y : ℝ} (h : cell114.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell114 check114 h
def cell113 : Cell := gridCell 64 3 30
theorem check113 : PinnStaged.check cell113 = true := by
  decide +kernel
theorem bound113 {x y : ℝ} (h : cell113.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell113 check113 h
def cell112 : Cell := gridCell 64 3 31
theorem check112 : PinnStaged.check cell112 = true := by
  decide +kernel
theorem bound112 {x y : ℝ} (h : cell112.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell112 check112 h
def RawShard0087Cells : List Cell := [cell115, cell114, cell113, cell112]
theorem RawShard0087Valid : ValidCells RawShard0087Cells := by
  intro c hc x y h
  simp only [RawShard0087Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h115 | h114 | h113 | h112
  · subst c
    exact bound115 h
  · subst c
    exact bound114 h
  · subst c
    exact bound113 h
  · subst c
    exact bound112 h
#print axioms RawShard0087Valid
end PinnCertFarm
