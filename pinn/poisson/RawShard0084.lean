import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell127 : Cell := gridCell 64 0 28
theorem check127 : PinnStaged.check cell127 = true := by
  decide +kernel
theorem bound127 {x y : ℝ} (h : cell127.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell127 check127 h
def cell126 : Cell := gridCell 64 0 29
theorem check126 : PinnStaged.check cell126 = true := by
  decide +kernel
theorem bound126 {x y : ℝ} (h : cell126.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell126 check126 h
def cell125 : Cell := gridCell 64 1 28
theorem check125 : PinnStaged.check cell125 = true := by
  decide +kernel
theorem bound125 {x y : ℝ} (h : cell125.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell125 check125 h
def cell124 : Cell := gridCell 64 1 29
theorem check124 : PinnStaged.check cell124 = true := by
  decide +kernel
theorem bound124 {x y : ℝ} (h : cell124.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell124 check124 h
def RawShard0084Cells : List Cell := [cell127, cell126, cell125, cell124]
theorem RawShard0084Valid : ValidCells RawShard0084Cells := by
  intro c hc x y h
  simp only [RawShard0084Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h127 | h126 | h125 | h124
  · subst c
    exact bound127 h
  · subst c
    exact bound126 h
  · subst c
    exact bound125 h
  · subst c
    exact bound124 h
#print axioms RawShard0084Valid
end PinnCertFarm
