import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1309 : Cell := gridCell 64 14 18
theorem check1309 : PinnStaged.check cell1309 = true := by
  decide +kernel
theorem bound1309 {x y : ℝ} (h : cell1309.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1309 check1309 h
def cell1308 : Cell := gridCell 64 14 19
theorem check1308 : PinnStaged.check cell1308 = true := by
  decide +kernel
theorem bound1308 {x y : ℝ} (h : cell1308.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1308 check1308 h
def cell1307 : Cell := gridCell 64 15 18
theorem check1307 : PinnStaged.check cell1307 = true := by
  decide +kernel
theorem bound1307 {x y : ℝ} (h : cell1307.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1307 check1307 h
def cell1306 : Cell := gridCell 64 15 19
theorem check1306 : PinnStaged.check cell1306 = true := by
  decide +kernel
theorem bound1306 {x y : ℝ} (h : cell1306.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1306 check1306 h
def RawShard0107Cells : List Cell := [cell1309, cell1308, cell1307, cell1306]
theorem RawShard0107Valid : ValidCells RawShard0107Cells := by
  intro c hc x y h
  simp only [RawShard0107Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1309 | h1308 | h1307 | h1306
  · subst c
    exact bound1309 h
  · subst c
    exact bound1308 h
  · subst c
    exact bound1307 h
  · subst c
    exact bound1306 h
#print axioms RawShard0107Valid
end PinnCertFarm
