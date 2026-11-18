import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell83 : Cell := gridCell 64 2 22
theorem check83 : PinnStaged.check cell83 = true := by
  decide +kernel
theorem bound83 {x y : ℝ} (h : cell83.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell83 check83 h
def cell82 : Cell := gridCell 64 2 23
theorem check82 : PinnStaged.check cell82 = true := by
  decide +kernel
theorem bound82 {x y : ℝ} (h : cell82.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell82 check82 h
def cell81 : Cell := gridCell 64 3 22
theorem check81 : PinnStaged.check cell81 = true := by
  decide +kernel
theorem bound81 {x y : ℝ} (h : cell81.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell81 check81 h
def cell80 : Cell := gridCell 64 3 23
theorem check80 : PinnStaged.check cell80 = true := by
  decide +kernel
theorem bound80 {x y : ℝ} (h : cell80.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell80 check80 h
def RawShard0071Cells : List Cell := [cell83, cell82, cell81, cell80]
theorem RawShard0071Valid : ValidCells RawShard0071Cells := by
  intro c hc x y h
  simp only [RawShard0071Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h83 | h82 | h81 | h80
  · subst c
    exact bound83 h
  · subst c
    exact bound82 h
  · subst c
    exact bound81 h
  · subst c
    exact bound80 h
#print axioms RawShard0071Valid
end PinnCertFarm
