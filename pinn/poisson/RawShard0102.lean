import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell899 : Cell := gridCell 64 10 20
theorem check899 : PinnStaged.check cell899 = true := by
  decide +kernel
theorem bound899 {x y : ℝ} (h : cell899.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell899 check899 h
def cell898 : Cell := gridCell 64 10 21
theorem check898 : PinnStaged.check cell898 = true := by
  decide +kernel
theorem bound898 {x y : ℝ} (h : cell898.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell898 check898 h
def cell897 : Cell := gridCell 64 11 20
theorem check897 : PinnStaged.check cell897 = true := by
  decide +kernel
theorem bound897 {x y : ℝ} (h : cell897.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell897 check897 h
def cell896 : Cell := gridCell 64 11 21
theorem check896 : PinnStaged.check cell896 = true := by
  decide +kernel
theorem bound896 {x y : ℝ} (h : cell896.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell896 check896 h
def RawShard0102Cells : List Cell := [cell899, cell898, cell897, cell896]
theorem RawShard0102Valid : ValidCells RawShard0102Cells := by
  intro c hc x y h
  simp only [RawShard0102Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h899 | h898 | h897 | h896
  · subst c
    exact bound899 h
  · subst c
    exact bound898 h
  · subst c
    exact bound897 h
  · subst c
    exact bound896 h
#print axioms RawShard0102Valid
end PinnCertFarm
