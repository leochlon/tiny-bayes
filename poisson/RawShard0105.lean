import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1317 : Cell := gridCell 64 12 18
theorem check1317 : PinnStaged.check cell1317 = true := by
  decide +kernel
theorem bound1317 {x y : ℝ} (h : cell1317.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1317 check1317 h
def cell1316 : Cell := gridCell 64 12 19
theorem check1316 : PinnStaged.check cell1316 = true := by
  decide +kernel
theorem bound1316 {x y : ℝ} (h : cell1316.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1316 check1316 h
def cell1315 : Cell := gridCell 64 13 18
theorem check1315 : PinnStaged.check cell1315 = true := by
  decide +kernel
theorem bound1315 {x y : ℝ} (h : cell1315.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1315 check1315 h
def cell1314 : Cell := gridCell 64 13 19
theorem check1314 : PinnStaged.check cell1314 = true := by
  decide +kernel
theorem bound1314 {x y : ℝ} (h : cell1314.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1314 check1314 h
def RawShard0105Cells : List Cell := [cell1317, cell1316, cell1315, cell1314]
theorem RawShard0105Valid : ValidCells RawShard0105Cells := by
  intro c hc x y h
  simp only [RawShard0105Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1317 | h1316 | h1315 | h1314
  · subst c
    exact bound1317 h
  · subst c
    exact bound1316 h
  · subst c
    exact bound1315 h
  · subst c
    exact bound1314 h
#print axioms RawShard0105Valid
end PinnCertFarm
