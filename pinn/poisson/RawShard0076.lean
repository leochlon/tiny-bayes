import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell486 : Cell := gridCell 64 4 20
theorem check486 : PinnStaged.check cell486 = true := by
  decide +kernel
theorem bound486 {x y : ℝ} (h : cell486.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell486 check486 h
def cell485 : Cell := gridCell 64 4 21
theorem check485 : PinnStaged.check cell485 = true := by
  decide +kernel
theorem bound485 {x y : ℝ} (h : cell485.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell485 check485 h
def cell484 : Cell := gridCell 64 5 20
theorem check484 : PinnStaged.check cell484 = true := by
  decide +kernel
theorem bound484 {x y : ℝ} (h : cell484.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell484 check484 h
def cell483 : Cell := gridCell 64 5 21
theorem check483 : PinnStaged.check cell483 = true := by
  decide +kernel
theorem bound483 {x y : ℝ} (h : cell483.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell483 check483 h
def RawShard0076Cells : List Cell := [cell486, cell485, cell484, cell483]
theorem RawShard0076Valid : ValidCells RawShard0076Cells := by
  intro c hc x y h
  simp only [RawShard0076Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h486 | h485 | h484 | h483
  · subst c
    exact bound486 h
  · subst c
    exact bound485 h
  · subst c
    exact bound484 h
  · subst c
    exact bound483 h
#print axioms RawShard0076Valid
end PinnCertFarm
