import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1361 : Cell := gridCell 64 14 28
theorem check1361 : PinnStaged.check cell1361 = true := by
  decide +kernel
theorem bound1361 {x y : ℝ} (h : cell1361.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1361 check1361 h
def cell1360 : Cell := gridCell 64 14 29
theorem check1360 : PinnStaged.check cell1360 = true := by
  decide +kernel
theorem bound1360 {x y : ℝ} (h : cell1360.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1360 check1360 h
def cell1359 : Cell := gridCell 64 15 28
theorem check1359 : PinnStaged.check cell1359 = true := by
  decide +kernel
theorem bound1359 {x y : ℝ} (h : cell1359.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1359 check1359 h
def cell1358 : Cell := gridCell 64 15 29
theorem check1358 : PinnStaged.check cell1358 = true := by
  decide +kernel
theorem bound1358 {x y : ℝ} (h : cell1358.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1358 check1358 h
def RawShard0126Cells : List Cell := [cell1361, cell1360, cell1359, cell1358]
theorem RawShard0126Valid : ValidCells RawShard0126Cells := by
  intro c hc x y h
  simp only [RawShard0126Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1361 | h1360 | h1359 | h1358
  · subst c
    exact bound1361 h
  · subst c
    exact bound1360 h
  · subst c
    exact bound1359 h
  · subst c
    exact bound1358 h
#print axioms RawShard0126Valid
end PinnCertFarm
