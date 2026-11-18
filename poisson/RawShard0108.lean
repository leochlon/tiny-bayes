import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1337 : Cell := gridCell 64 12 20
theorem check1337 : PinnStaged.check cell1337 = true := by
  decide +kernel
theorem bound1337 {x y : ℝ} (h : cell1337.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1337 check1337 h
def cell1336 : Cell := gridCell 64 12 21
theorem check1336 : PinnStaged.check cell1336 = true := by
  decide +kernel
theorem bound1336 {x y : ℝ} (h : cell1336.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1336 check1336 h
def cell1335 : Cell := gridCell 64 13 20
theorem check1335 : PinnStaged.check cell1335 = true := by
  decide +kernel
theorem bound1335 {x y : ℝ} (h : cell1335.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1335 check1335 h
def cell1334 : Cell := gridCell 64 13 21
theorem check1334 : PinnStaged.check cell1334 = true := by
  decide +kernel
theorem bound1334 {x y : ℝ} (h : cell1334.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1334 check1334 h
def RawShard0108Cells : List Cell := [cell1337, cell1336, cell1335, cell1334]
theorem RawShard0108Valid : ValidCells RawShard0108Cells := by
  intro c hc x y h
  simp only [RawShard0108Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1337 | h1336 | h1335 | h1334
  · subst c
    exact bound1337 h
  · subst c
    exact bound1336 h
  · subst c
    exact bound1335 h
  · subst c
    exact bound1334 h
#print axioms RawShard0108Valid
end PinnCertFarm
