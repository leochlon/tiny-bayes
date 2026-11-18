import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3867 : Cell := gridCell 64 35 2
theorem check3867 : PinnStaged.check cell3867 = true := by
  decide +kernel
theorem bound3867 {x y : ℝ} (h : cell3867.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3867 check3867 h
def cell3866 : Cell := gridCell 64 35 3
theorem check3866 : PinnStaged.check cell3866 = true := by
  decide +kernel
theorem bound3866 {x y : ℝ} (h : cell3866.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3866 check3866 h
def cell3897 : Cell := gridCell 64 32 4
theorem check3897 : PinnStaged.check cell3897 = true := by
  decide +kernel
theorem bound3897 {x y : ℝ} (h : cell3897.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3897 check3897 h
def cell3896 : Cell := gridCell 64 32 5
theorem check3896 : PinnStaged.check cell3896 = true := by
  decide +kernel
theorem bound3896 {x y : ℝ} (h : cell3896.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3896 check3896 h
def RawShard0970Cells : List Cell := [cell3867, cell3866, cell3897, cell3896]
theorem RawShard0970Valid : ValidCells RawShard0970Cells := by
  intro c hc x y h
  simp only [RawShard0970Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3867 | h3866 | h3897 | h3896
  · subst c
    exact bound3867 h
  · subst c
    exact bound3866 h
  · subst c
    exact bound3897 h
  · subst c
    exact bound3896 h
#print axioms RawShard0970Valid
end PinnCertFarm
