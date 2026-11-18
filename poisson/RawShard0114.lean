import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell915 : Cell := gridCell 64 10 24
theorem check915 : PinnStaged.check cell915 = true := by
  decide +kernel
theorem bound915 {x y : ℝ} (h : cell915.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell915 check915 h
def cell914 : Cell := gridCell 64 10 25
theorem check914 : PinnStaged.check cell914 = true := by
  decide +kernel
theorem bound914 {x y : ℝ} (h : cell914.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell914 check914 h
def cell913 : Cell := gridCell 64 11 24
theorem check913 : PinnStaged.check cell913 = true := by
  decide +kernel
theorem bound913 {x y : ℝ} (h : cell913.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell913 check913 h
def cell912 : Cell := gridCell 64 11 25
theorem check912 : PinnStaged.check cell912 = true := by
  decide +kernel
theorem bound912 {x y : ℝ} (h : cell912.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell912 check912 h
def RawShard0114Cells : List Cell := [cell915, cell914, cell913, cell912]
theorem RawShard0114Valid : ValidCells RawShard0114Cells := by
  intro c hc x y h
  simp only [RawShard0114Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h915 | h914 | h913 | h912
  · subst c
    exact bound915 h
  · subst c
    exact bound914 h
  · subst c
    exact bound913 h
  · subst c
    exact bound912 h
#print axioms RawShard0114Valid
end PinnCertFarm
