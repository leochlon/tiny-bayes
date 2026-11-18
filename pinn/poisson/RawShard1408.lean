import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4091 : Cell := gridCell 128 71 94
theorem check4091 : PinnStaged.check cell4091 = true := by
  decide +kernel
theorem bound4091 {x y : ℝ} (h : cell4091.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4091 check4091 h
def cell4090 : Cell := gridCell 128 71 95
theorem check4090 : PinnStaged.check cell4090 = true := by
  decide +kernel
theorem bound4090 {x y : ℝ} (h : cell4090.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4090 check4090 h
def cell4648 : Cell := gridCell 128 72 80
theorem check4648 : PinnStaged.check cell4648 = true := by
  decide +kernel
theorem bound4648 {x y : ℝ} (h : cell4648.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4648 check4648 h
def cell4647 : Cell := gridCell 128 72 81
theorem check4647 : PinnStaged.check cell4647 = true := by
  decide +kernel
theorem bound4647 {x y : ℝ} (h : cell4647.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4647 check4647 h
def RawShard1408Cells : List Cell := [cell4091, cell4090, cell4648, cell4647]
theorem RawShard1408Valid : ValidCells RawShard1408Cells := by
  intro c hc x y h
  simp only [RawShard1408Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4091 | h4090 | h4648 | h4647
  · subst c
    exact bound4091 h
  · subst c
    exact bound4090 h
  · subst c
    exact bound4648 h
  · subst c
    exact bound4647 h
#print axioms RawShard1408Valid
end PinnCertFarm
