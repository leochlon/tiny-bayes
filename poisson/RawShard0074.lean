import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell462 : Cell := gridCell 64 6 16
theorem check462 : PinnStaged.check cell462 = true := by
  decide +kernel
theorem bound462 {x y : ℝ} (h : cell462.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell462 check462 h
def cell461 : Cell := gridCell 64 6 17
theorem check461 : PinnStaged.check cell461 = true := by
  decide +kernel
theorem bound461 {x y : ℝ} (h : cell461.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell461 check461 h
def cell460 : Cell := gridCell 64 7 16
theorem check460 : PinnStaged.check cell460 = true := by
  decide +kernel
theorem bound460 {x y : ℝ} (h : cell460.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell460 check460 h
def cell459 : Cell := gridCell 64 7 17
theorem check459 : PinnStaged.check cell459 = true := by
  decide +kernel
theorem bound459 {x y : ℝ} (h : cell459.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell459 check459 h
def RawShard0074Cells : List Cell := [cell462, cell461, cell460, cell459]
theorem RawShard0074Valid : ValidCells RawShard0074Cells := by
  intro c hc x y h
  simp only [RawShard0074Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h462 | h461 | h460 | h459
  · subst c
    exact bound462 h
  · subst c
    exact bound461 h
  · subst c
    exact bound460 h
  · subst c
    exact bound459 h
#print axioms RawShard0074Valid
end PinnCertFarm
