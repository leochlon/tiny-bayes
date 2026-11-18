import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4115 : Cell := gridCell 128 69 89
theorem check4115 : PinnStaged.check cell4115 = true := by
  decide +kernel
theorem bound4115 {x y : ℝ} (h : cell4115.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4115 check4115 h
def cell4114 : Cell := gridCell 128 68 90
theorem check4114 : PinnStaged.check cell4114 = true := by
  decide +kernel
theorem bound4114 {x y : ℝ} (h : cell4114.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4114 check4114 h
def cell4113 : Cell := gridCell 128 68 91
theorem check4113 : PinnStaged.check cell4113 = true := by
  decide +kernel
theorem bound4113 {x y : ℝ} (h : cell4113.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4113 check4113 h
def cell4112 : Cell := gridCell 128 69 90
theorem check4112 : PinnStaged.check cell4112 = true := by
  decide +kernel
theorem bound4112 {x y : ℝ} (h : cell4112.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4112 check4112 h
def RawShard1402Cells : List Cell := [cell4115, cell4114, cell4113, cell4112]
theorem RawShard1402Valid : ValidCells RawShard1402Cells := by
  intro c hc x y h
  simp only [RawShard1402Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4115 | h4114 | h4113 | h4112
  · subst c
    exact bound4115 h
  · subst c
    exact bound4114 h
  · subst c
    exact bound4113 h
  · subst c
    exact bound4112 h
#print axioms RawShard1402Valid
end PinnCertFarm
