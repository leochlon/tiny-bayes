import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4598 : Cell := gridCell 128 77 84
theorem check4598 : PinnStaged.check cell4598 = true := by
  decide +kernel
theorem bound4598 {x y : ℝ} (h : cell4598.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4598 check4598 h
def cell4597 : Cell := gridCell 128 77 85
theorem check4597 : PinnStaged.check cell4597 = true := by
  decide +kernel
theorem bound4597 {x y : ℝ} (h : cell4597.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4597 check4597 h
def cell4596 : Cell := gridCell 128 76 86
theorem check4596 : PinnStaged.check cell4596 = true := by
  decide +kernel
theorem bound4596 {x y : ℝ} (h : cell4596.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4596 check4596 h
def cell4595 : Cell := gridCell 128 76 87
theorem check4595 : PinnStaged.check cell4595 = true := by
  decide +kernel
theorem bound4595 {x y : ℝ} (h : cell4595.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4595 check4595 h
def RawShard1421Cells : List Cell := [cell4598, cell4597, cell4596, cell4595]
theorem RawShard1421Valid : ValidCells RawShard1421Cells := by
  intro c hc x y h
  simp only [RawShard1421Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4598 | h4597 | h4596 | h4595
  · subst c
    exact bound4598 h
  · subst c
    exact bound4597 h
  · subst c
    exact bound4596 h
  · subst c
    exact bound4595 h
#print axioms RawShard1421Valid
end PinnCertFarm
