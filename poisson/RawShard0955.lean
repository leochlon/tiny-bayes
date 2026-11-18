import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3823 : Cell := gridCell 256 119 254
theorem check3823 : PinnStaged.check cell3823 = true := by
  decide +kernel
theorem bound3823 {x y : ℝ} (h : cell3823.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3823 check3823 h
def cell3822 : Cell := gridCell 256 119 255
theorem check3822 : PinnStaged.check cell3822 = true := by
  decide +kernel
theorem bound3822 {x y : ℝ} (h : cell3822.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3822 check3822 h
def cell3821 : Cell := gridCell 128 60 120
theorem check3821 : PinnStaged.check cell3821 = true := by
  decide +kernel
theorem bound3821 {x y : ℝ} (h : cell3821.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3821 check3821 h
def cell3820 : Cell := gridCell 128 60 121
theorem check3820 : PinnStaged.check cell3820 = true := by
  decide +kernel
theorem bound3820 {x y : ℝ} (h : cell3820.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3820 check3820 h
def RawShard0955Cells : List Cell := [cell3823, cell3822, cell3821, cell3820]
theorem RawShard0955Valid : ValidCells RawShard0955Cells := by
  intro c hc x y h
  simp only [RawShard0955Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3823 | h3822 | h3821 | h3820
  · subst c
    exact bound3823 h
  · subst c
    exact bound3822 h
  · subst c
    exact bound3821 h
  · subst c
    exact bound3820 h
#print axioms RawShard0955Valid
end PinnCertFarm
