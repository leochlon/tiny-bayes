import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell923 : Cell := gridCell 64 8 24
theorem check923 : PinnStaged.check cell923 = true := by
  decide +kernel
theorem bound923 {x y : ℝ} (h : cell923.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell923 check923 h
def cell922 : Cell := gridCell 64 8 25
theorem check922 : PinnStaged.check cell922 = true := by
  decide +kernel
theorem bound922 {x y : ℝ} (h : cell922.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell922 check922 h
def cell921 : Cell := gridCell 64 9 24
theorem check921 : PinnStaged.check cell921 = true := by
  decide +kernel
theorem bound921 {x y : ℝ} (h : cell921.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell921 check921 h
def cell920 : Cell := gridCell 64 9 25
theorem check920 : PinnStaged.check cell920 = true := by
  decide +kernel
theorem bound920 {x y : ℝ} (h : cell920.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell920 check920 h
def RawShard0112Cells : List Cell := [cell923, cell922, cell921, cell920]
theorem RawShard0112Valid : ValidCells RawShard0112Cells := by
  intro c hc x y h
  simp only [RawShard0112Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h923 | h922 | h921 | h920
  · subst c
    exact bound923 h
  · subst c
    exact bound922 h
  · subst c
    exact bound921 h
  · subst c
    exact bound920 h
#print axioms RawShard0112Valid
end PinnCertFarm
