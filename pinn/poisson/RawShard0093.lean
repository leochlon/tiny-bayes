import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell514 : Cell := gridCell 64 4 30
theorem check514 : PinnStaged.check cell514 = true := by
  decide +kernel
theorem bound514 {x y : ℝ} (h : cell514.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell514 check514 h
def cell513 : Cell := gridCell 64 4 31
theorem check513 : PinnStaged.check cell513 = true := by
  decide +kernel
theorem bound513 {x y : ℝ} (h : cell513.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell513 check513 h
def cell512 : Cell := gridCell 64 5 30
theorem check512 : PinnStaged.check cell512 = true := by
  decide +kernel
theorem bound512 {x y : ℝ} (h : cell512.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell512 check512 h
def cell511 : Cell := gridCell 64 5 31
theorem check511 : PinnStaged.check cell511 = true := by
  decide +kernel
theorem bound511 {x y : ℝ} (h : cell511.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell511 check511 h
def RawShard0093Cells : List Cell := [cell514, cell513, cell512, cell511]
theorem RawShard0093Valid : ValidCells RawShard0093Cells := by
  intro c hc x y h
  simp only [RawShard0093Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h514 | h513 | h512 | h511
  · subst c
    exact bound514 h
  · subst c
    exact bound513 h
  · subst c
    exact bound512 h
  · subst c
    exact bound511 h
#print axioms RawShard0093Valid
end PinnCertFarm
