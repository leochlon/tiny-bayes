import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell939 : Cell := gridCell 64 8 28
theorem check939 : PinnStaged.check cell939 = true := by
  decide +kernel
theorem bound939 {x y : ℝ} (h : cell939.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell939 check939 h
def cell938 : Cell := gridCell 64 8 29
theorem check938 : PinnStaged.check cell938 = true := by
  decide +kernel
theorem bound938 {x y : ℝ} (h : cell938.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell938 check938 h
def cell937 : Cell := gridCell 64 9 28
theorem check937 : PinnStaged.check cell937 = true := by
  decide +kernel
theorem bound937 {x y : ℝ} (h : cell937.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell937 check937 h
def cell936 : Cell := gridCell 64 9 29
theorem check936 : PinnStaged.check cell936 = true := by
  decide +kernel
theorem bound936 {x y : ℝ} (h : cell936.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell936 check936 h
def RawShard0116Cells : List Cell := [cell939, cell938, cell937, cell936]
theorem RawShard0116Valid : ValidCells RawShard0116Cells := by
  intro c hc x y h
  simp only [RawShard0116Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h939 | h938 | h937 | h936
  · subst c
    exact bound939 h
  · subst c
    exact bound938 h
  · subst c
    exact bound937 h
  · subst c
    exact bound936 h
#print axioms RawShard0116Valid
end PinnCertFarm
