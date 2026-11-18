import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4119 : Cell := gridCell 64 33 47
theorem check4119 : PinnStaged.check cell4119 = true := by
  decide +kernel
theorem bound4119 {x y : ℝ} (h : cell4119.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4119 check4119 h
def cell4118 : Cell := gridCell 128 68 88
theorem check4118 : PinnStaged.check cell4118 = true := by
  decide +kernel
theorem bound4118 {x y : ℝ} (h : cell4118.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4118 check4118 h
def cell4117 : Cell := gridCell 128 68 89
theorem check4117 : PinnStaged.check cell4117 = true := by
  decide +kernel
theorem bound4117 {x y : ℝ} (h : cell4117.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4117 check4117 h
def cell4116 : Cell := gridCell 128 69 88
theorem check4116 : PinnStaged.check cell4116 = true := by
  decide +kernel
theorem bound4116 {x y : ℝ} (h : cell4116.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4116 check4116 h
def RawShard1401Cells : List Cell := [cell4119, cell4118, cell4117, cell4116]
theorem RawShard1401Valid : ValidCells RawShard1401Cells := by
  intro c hc x y h
  simp only [RawShard1401Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4119 | h4118 | h4117 | h4116
  · subst c
    exact bound4119 h
  · subst c
    exact bound4118 h
  · subst c
    exact bound4117 h
  · subst c
    exact bound4116 h
#print axioms RawShard1401Valid
end PinnCertFarm
