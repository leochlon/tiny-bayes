import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell466 : Cell := gridCell 64 4 18
theorem check466 : PinnStaged.check cell466 = true := by
  decide +kernel
theorem bound466 {x y : ℝ} (h : cell466.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell466 check466 h
def cell465 : Cell := gridCell 64 4 19
theorem check465 : PinnStaged.check cell465 = true := by
  decide +kernel
theorem bound465 {x y : ℝ} (h : cell465.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell465 check465 h
def cell464 : Cell := gridCell 64 5 18
theorem check464 : PinnStaged.check cell464 = true := by
  decide +kernel
theorem bound464 {x y : ℝ} (h : cell464.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell464 check464 h
def cell463 : Cell := gridCell 64 5 19
theorem check463 : PinnStaged.check cell463 = true := by
  decide +kernel
theorem bound463 {x y : ℝ} (h : cell463.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell463 check463 h
def RawShard0073Cells : List Cell := [cell466, cell465, cell464, cell463]
theorem RawShard0073Valid : ValidCells RawShard0073Cells := by
  intro c hc x y h
  simp only [RawShard0073Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h466 | h465 | h464 | h463
  · subst c
    exact bound466 h
  · subst c
    exact bound465 h
  · subst c
    exact bound464 h
  · subst c
    exact bound463 h
#print axioms RawShard0073Valid
end PinnCertFarm
