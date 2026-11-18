import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell891 : Cell := gridCell 64 8 16
theorem check891 : PinnStaged.check cell891 = true := by
  decide +kernel
theorem bound891 {x y : ℝ} (h : cell891.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell891 check891 h
def cell890 : Cell := gridCell 64 8 17
theorem check890 : PinnStaged.check cell890 = true := by
  decide +kernel
theorem bound890 {x y : ℝ} (h : cell890.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell890 check890 h
def cell889 : Cell := gridCell 64 9 16
theorem check889 : PinnStaged.check cell889 = true := by
  decide +kernel
theorem bound889 {x y : ℝ} (h : cell889.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell889 check889 h
def cell888 : Cell := gridCell 64 9 17
theorem check888 : PinnStaged.check cell888 = true := by
  decide +kernel
theorem bound888 {x y : ℝ} (h : cell888.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell888 check888 h
def RawShard0096Cells : List Cell := [cell891, cell890, cell889, cell888]
theorem RawShard0096Valid : ValidCells RawShard0096Cells := by
  intro c hc x y h
  simp only [RawShard0096Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h891 | h890 | h889 | h888
  · subst c
    exact bound891 h
  · subst c
    exact bound890 h
  · subst c
    exact bound889 h
  · subst c
    exact bound888 h
#print axioms RawShard0096Valid
end PinnCertFarm
