import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell935 : Cell := gridCell 64 8 30
theorem check935 : PinnStaged.check cell935 = true := by
  decide +kernel
theorem bound935 {x y : ℝ} (h : cell935.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell935 check935 h
def cell934 : Cell := gridCell 64 8 31
theorem check934 : PinnStaged.check cell934 = true := by
  decide +kernel
theorem bound934 {x y : ℝ} (h : cell934.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell934 check934 h
def cell933 : Cell := gridCell 64 9 30
theorem check933 : PinnStaged.check cell933 = true := by
  decide +kernel
theorem bound933 {x y : ℝ} (h : cell933.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell933 check933 h
def cell932 : Cell := gridCell 64 9 31
theorem check932 : PinnStaged.check cell932 = true := by
  decide +kernel
theorem bound932 {x y : ℝ} (h : cell932.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell932 check932 h
def RawShard0117Cells : List Cell := [cell935, cell934, cell933, cell932]
theorem RawShard0117Valid : ValidCells RawShard0117Cells := by
  intro c hc x y h
  simp only [RawShard0117Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h935 | h934 | h933 | h932
  · subst c
    exact bound935 h
  · subst c
    exact bound934 h
  · subst c
    exact bound933 h
  · subst c
    exact bound932 h
#print axioms RawShard0117Valid
end PinnCertFarm
