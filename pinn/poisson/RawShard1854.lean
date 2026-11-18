import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6334 : Cell := gridCell 128 102 83
theorem check6334 : PinnStaged.check cell6334 = true := by
  decide +kernel
theorem bound6334 {x y : ℝ} (h : cell6334.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6334 check6334 h
def cell6333 : Cell := gridCell 128 103 82
theorem check6333 : PinnStaged.check cell6333 = true := by
  decide +kernel
theorem bound6333 {x y : ℝ} (h : cell6333.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6333 check6333 h
def cell6332 : Cell := gridCell 128 103 83
theorem check6332 : PinnStaged.check cell6332 = true := by
  decide +kernel
theorem bound6332 {x y : ℝ} (h : cell6332.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6332 check6332 h
def cell6331 : Cell := gridCell 128 100 84
theorem check6331 : PinnStaged.check cell6331 = true := by
  decide +kernel
theorem bound6331 {x y : ℝ} (h : cell6331.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6331 check6331 h
def RawShard1854Cells : List Cell := [cell6334, cell6333, cell6332, cell6331]
theorem RawShard1854Valid : ValidCells RawShard1854Cells := by
  intro c hc x y h
  simp only [RawShard1854Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6334 | h6333 | h6332 | h6331
  · subst c
    exact bound6334 h
  · subst c
    exact bound6333 h
  · subst c
    exact bound6332 h
  · subst c
    exact bound6331 h
#print axioms RawShard1854Valid
end PinnCertFarm
