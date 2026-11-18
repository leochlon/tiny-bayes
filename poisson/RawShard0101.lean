import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell903 : Cell := gridCell 64 8 22
theorem check903 : PinnStaged.check cell903 = true := by
  decide +kernel
theorem bound903 {x y : ℝ} (h : cell903.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell903 check903 h
def cell902 : Cell := gridCell 64 8 23
theorem check902 : PinnStaged.check cell902 = true := by
  decide +kernel
theorem bound902 {x y : ℝ} (h : cell902.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell902 check902 h
def cell901 : Cell := gridCell 64 9 22
theorem check901 : PinnStaged.check cell901 = true := by
  decide +kernel
theorem bound901 {x y : ℝ} (h : cell901.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell901 check901 h
def cell900 : Cell := gridCell 64 9 23
theorem check900 : PinnStaged.check cell900 = true := by
  decide +kernel
theorem bound900 {x y : ℝ} (h : cell900.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell900 check900 h
def RawShard0101Cells : List Cell := [cell903, cell902, cell901, cell900]
theorem RawShard0101Valid : ValidCells RawShard0101Cells := by
  intro c hc x y h
  simp only [RawShard0101Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h903 | h902 | h901 | h900
  · subst c
    exact bound903 h
  · subst c
    exact bound902 h
  · subst c
    exact bound901 h
  · subst c
    exact bound900 h
#print axioms RawShard0101Valid
end PinnCertFarm
