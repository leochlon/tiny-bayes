import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell887 : Cell := gridCell 64 8 18
theorem check887 : PinnStaged.check cell887 = true := by
  decide +kernel
theorem bound887 {x y : ℝ} (h : cell887.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell887 check887 h
def cell886 : Cell := gridCell 64 8 19
theorem check886 : PinnStaged.check cell886 = true := by
  decide +kernel
theorem bound886 {x y : ℝ} (h : cell886.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell886 check886 h
def cell885 : Cell := gridCell 64 9 18
theorem check885 : PinnStaged.check cell885 = true := by
  decide +kernel
theorem bound885 {x y : ℝ} (h : cell885.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell885 check885 h
def cell884 : Cell := gridCell 64 9 19
theorem check884 : PinnStaged.check cell884 = true := by
  decide +kernel
theorem bound884 {x y : ℝ} (h : cell884.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell884 check884 h
def RawShard0097Cells : List Cell := [cell887, cell886, cell885, cell884]
theorem RawShard0097Valid : ValidCells RawShard0097Cells := by
  intro c hc x y h
  simp only [RawShard0097Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h887 | h886 | h885 | h884
  · subst c
    exact bound887 h
  · subst c
    exact bound886 h
  · subst c
    exact bound885 h
  · subst c
    exact bound884 h
#print axioms RawShard0097Valid
end PinnCertFarm
