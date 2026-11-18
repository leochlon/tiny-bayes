import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3344 : Cell := gridCell 64 28 4
theorem check3344 : PinnStaged.check cell3344 = true := by
  decide +kernel
theorem bound3344 {x y : ℝ} (h : cell3344.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3344 check3344 h
def cell3343 : Cell := gridCell 64 28 5
theorem check3343 : PinnStaged.check cell3343 = true := by
  decide +kernel
theorem bound3343 {x y : ℝ} (h : cell3343.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3343 check3343 h
def cell3342 : Cell := gridCell 64 29 4
theorem check3342 : PinnStaged.check cell3342 = true := by
  decide +kernel
theorem bound3342 {x y : ℝ} (h : cell3342.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3342 check3342 h
def cell3341 : Cell := gridCell 64 29 5
theorem check3341 : PinnStaged.check cell3341 = true := by
  decide +kernel
theorem bound3341 {x y : ℝ} (h : cell3341.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3341 check3341 h
def RawShard0172Cells : List Cell := [cell3344, cell3343, cell3342, cell3341]
theorem RawShard0172Valid : ValidCells RawShard0172Cells := by
  intro c hc x y h
  simp only [RawShard0172Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3344 | h3343 | h3342 | h3341
  · subst c
    exact bound3344 h
  · subst c
    exact bound3343 h
  · subst c
    exact bound3342 h
  · subst c
    exact bound3341 h
#print axioms RawShard0172Valid
end PinnCertFarm
