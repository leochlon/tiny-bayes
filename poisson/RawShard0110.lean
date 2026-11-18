import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1329 : Cell := gridCell 64 14 20
theorem check1329 : PinnStaged.check cell1329 = true := by
  decide +kernel
theorem bound1329 {x y : ℝ} (h : cell1329.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1329 check1329 h
def cell1328 : Cell := gridCell 64 14 21
theorem check1328 : PinnStaged.check cell1328 = true := by
  decide +kernel
theorem bound1328 {x y : ℝ} (h : cell1328.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1328 check1328 h
def cell1327 : Cell := gridCell 64 15 20
theorem check1327 : PinnStaged.check cell1327 = true := by
  decide +kernel
theorem bound1327 {x y : ℝ} (h : cell1327.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1327 check1327 h
def cell1326 : Cell := gridCell 64 15 21
theorem check1326 : PinnStaged.check cell1326 = true := by
  decide +kernel
theorem bound1326 {x y : ℝ} (h : cell1326.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1326 check1326 h
def RawShard0110Cells : List Cell := [cell1329, cell1328, cell1327, cell1326]
theorem RawShard0110Valid : ValidCells RawShard0110Cells := by
  intro c hc x y h
  simp only [RawShard0110Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1329 | h1328 | h1327 | h1326
  · subst c
    exact bound1329 h
  · subst c
    exact bound1328 h
  · subst c
    exact bound1327 h
  · subst c
    exact bound1326 h
#print axioms RawShard0110Valid
end PinnCertFarm
