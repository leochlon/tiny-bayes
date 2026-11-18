import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell482 : Cell := gridCell 64 4 22
theorem check482 : PinnStaged.check cell482 = true := by
  decide +kernel
theorem bound482 {x y : ℝ} (h : cell482.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell482 check482 h
def cell481 : Cell := gridCell 64 4 23
theorem check481 : PinnStaged.check cell481 = true := by
  decide +kernel
theorem bound481 {x y : ℝ} (h : cell481.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell481 check481 h
def cell480 : Cell := gridCell 64 5 22
theorem check480 : PinnStaged.check cell480 = true := by
  decide +kernel
theorem bound480 {x y : ℝ} (h : cell480.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell480 check480 h
def cell479 : Cell := gridCell 64 5 23
theorem check479 : PinnStaged.check cell479 = true := by
  decide +kernel
theorem bound479 {x y : ℝ} (h : cell479.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell479 check479 h
def RawShard0077Cells : List Cell := [cell482, cell481, cell480, cell479]
theorem RawShard0077Valid : ValidCells RawShard0077Cells := by
  intro c hc x y h
  simp only [RawShard0077Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h482 | h481 | h480 | h479
  · subst c
    exact bound482 h
  · subst c
    exact bound481 h
  · subst c
    exact bound480 h
  · subst c
    exact bound479 h
#print axioms RawShard0077Valid
end PinnCertFarm
