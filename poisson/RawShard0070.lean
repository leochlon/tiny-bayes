import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell87 : Cell := gridCell 64 2 20
theorem check87 : PinnStaged.check cell87 = true := by
  decide +kernel
theorem bound87 {x y : ℝ} (h : cell87.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell87 check87 h
def cell86 : Cell := gridCell 64 2 21
theorem check86 : PinnStaged.check cell86 = true := by
  decide +kernel
theorem bound86 {x y : ℝ} (h : cell86.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell86 check86 h
def cell85 : Cell := gridCell 64 3 20
theorem check85 : PinnStaged.check cell85 = true := by
  decide +kernel
theorem bound85 {x y : ℝ} (h : cell85.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell85 check85 h
def cell84 : Cell := gridCell 64 3 21
theorem check84 : PinnStaged.check cell84 = true := by
  decide +kernel
theorem bound84 {x y : ℝ} (h : cell84.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell84 check84 h
def RawShard0070Cells : List Cell := [cell87, cell86, cell85, cell84]
theorem RawShard0070Valid : ValidCells RawShard0070Cells := by
  intro c hc x y h
  simp only [RawShard0070Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h87 | h86 | h85 | h84
  · subst c
    exact bound87 h
  · subst c
    exact bound86 h
  · subst c
    exact bound85 h
  · subst c
    exact bound84 h
#print axioms RawShard0070Valid
end PinnCertFarm
