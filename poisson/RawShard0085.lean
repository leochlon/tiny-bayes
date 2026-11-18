import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell123 : Cell := gridCell 64 0 30
theorem check123 : PinnStaged.check cell123 = true := by
  decide +kernel
theorem bound123 {x y : ℝ} (h : cell123.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell123 check123 h
def cell122 : Cell := gridCell 64 0 31
theorem check122 : PinnStaged.check cell122 = true := by
  decide +kernel
theorem bound122 {x y : ℝ} (h : cell122.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell122 check122 h
def cell121 : Cell := gridCell 64 1 30
theorem check121 : PinnStaged.check cell121 = true := by
  decide +kernel
theorem bound121 {x y : ℝ} (h : cell121.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell121 check121 h
def cell120 : Cell := gridCell 64 1 31
theorem check120 : PinnStaged.check cell120 = true := by
  decide +kernel
theorem bound120 {x y : ℝ} (h : cell120.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell120 check120 h
def RawShard0085Cells : List Cell := [cell123, cell122, cell121, cell120]
theorem RawShard0085Valid : ValidCells RawShard0085Cells := by
  intro c hc x y h
  simp only [RawShard0085Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h123 | h122 | h121 | h120
  · subst c
    exact bound123 h
  · subst c
    exact bound122 h
  · subst c
    exact bound121 h
  · subst c
    exact bound120 h
#print axioms RawShard0085Valid
end PinnCertFarm
