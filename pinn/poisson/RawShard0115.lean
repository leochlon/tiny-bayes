import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell911 : Cell := gridCell 64 10 26
theorem check911 : PinnStaged.check cell911 = true := by
  decide +kernel
theorem bound911 {x y : ℝ} (h : cell911.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell911 check911 h
def cell910 : Cell := gridCell 64 10 27
theorem check910 : PinnStaged.check cell910 = true := by
  decide +kernel
theorem bound910 {x y : ℝ} (h : cell910.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell910 check910 h
def cell909 : Cell := gridCell 64 11 26
theorem check909 : PinnStaged.check cell909 = true := by
  decide +kernel
theorem bound909 {x y : ℝ} (h : cell909.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell909 check909 h
def cell908 : Cell := gridCell 64 11 27
theorem check908 : PinnStaged.check cell908 = true := by
  decide +kernel
theorem bound908 {x y : ℝ} (h : cell908.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell908 check908 h
def RawShard0115Cells : List Cell := [cell911, cell910, cell909, cell908]
theorem RawShard0115Valid : ValidCells RawShard0115Cells := by
  intro c hc x y h
  simp only [RawShard0115Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h911 | h910 | h909 | h908
  · subst c
    exact bound911 h
  · subst c
    exact bound910 h
  · subst c
    exact bound909 h
  · subst c
    exact bound908 h
#print axioms RawShard0115Valid
end PinnCertFarm
