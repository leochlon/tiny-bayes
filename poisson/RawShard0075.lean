import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell458 : Cell := gridCell 64 6 18
theorem check458 : PinnStaged.check cell458 = true := by
  decide +kernel
theorem bound458 {x y : ℝ} (h : cell458.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell458 check458 h
def cell457 : Cell := gridCell 64 6 19
theorem check457 : PinnStaged.check cell457 = true := by
  decide +kernel
theorem bound457 {x y : ℝ} (h : cell457.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell457 check457 h
def cell456 : Cell := gridCell 64 7 18
theorem check456 : PinnStaged.check cell456 = true := by
  decide +kernel
theorem bound456 {x y : ℝ} (h : cell456.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell456 check456 h
def cell455 : Cell := gridCell 64 7 19
theorem check455 : PinnStaged.check cell455 = true := by
  decide +kernel
theorem bound455 {x y : ℝ} (h : cell455.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell455 check455 h
def RawShard0075Cells : List Cell := [cell458, cell457, cell456, cell455]
theorem RawShard0075Valid : ValidCells RawShard0075Cells := by
  intro c hc x y h
  simp only [RawShard0075Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h458 | h457 | h456 | h455
  · subst c
    exact bound458 h
  · subst c
    exact bound457 h
  · subst c
    exact bound456 h
  · subst c
    exact bound455 h
#print axioms RawShard0075Valid
end PinnCertFarm
