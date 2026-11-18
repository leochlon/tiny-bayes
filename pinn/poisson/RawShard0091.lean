import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell490 : Cell := gridCell 64 6 26
theorem check490 : PinnStaged.check cell490 = true := by
  decide +kernel
theorem bound490 {x y : ℝ} (h : cell490.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell490 check490 h
def cell489 : Cell := gridCell 64 6 27
theorem check489 : PinnStaged.check cell489 = true := by
  decide +kernel
theorem bound489 {x y : ℝ} (h : cell489.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell489 check489 h
def cell488 : Cell := gridCell 64 7 26
theorem check488 : PinnStaged.check cell488 = true := by
  decide +kernel
theorem bound488 {x y : ℝ} (h : cell488.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell488 check488 h
def cell487 : Cell := gridCell 64 7 27
theorem check487 : PinnStaged.check cell487 = true := by
  decide +kernel
theorem bound487 {x y : ℝ} (h : cell487.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell487 check487 h
def RawShard0091Cells : List Cell := [cell490, cell489, cell488, cell487]
theorem RawShard0091Valid : ValidCells RawShard0091Cells := by
  intro c hc x y h
  simp only [RawShard0091Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h490 | h489 | h488 | h487
  · subst c
    exact bound490 h
  · subst c
    exact bound489 h
  · subst c
    exact bound488 h
  · subst c
    exact bound487 h
#print axioms RawShard0091Valid
end PinnCertFarm
