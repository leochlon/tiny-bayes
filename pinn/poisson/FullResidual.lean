import GroupBound00
import GroupBound01
import GroupBound02
import GroupBound03
import GroupBound04
import GroupBound05
import GroupBound06
import GroupBound07
import GroupBound08
import GroupBound09
import GroupBound10
import GroupBound11
import GroupBound12
import GroupBound13
import GroupBound14
import GroupBound15
import GroupBound16
import GroupBound17
import GroupBound18
import GroupBound19
import GroupBound20
import GroupBound21
import GroupBound22
import GroupBound23
import GroupBound24
import GroupBound25
import GroupBound26
import GroupBound27
import GroupBound28
import GroupBound29
import GroupBound30
import GroupBound31
import GroupBound32
import GroupBound33
import GroupBound34
import GroupBound35
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
theorem allValid : ValidCells expectedCells := by
  unfold expectedCells
  simpa only [List.append_assoc] using (valid_append group00_expected_valid (valid_append group01_expected_valid (valid_append group02_expected_valid (valid_append group03_expected_valid (valid_append group04_expected_valid (valid_append group05_expected_valid (valid_append group06_expected_valid (valid_append group07_expected_valid (valid_append group08_expected_valid (valid_append group09_expected_valid (valid_append group10_expected_valid (valid_append group11_expected_valid (valid_append group12_expected_valid (valid_append group13_expected_valid (valid_append group14_expected_valid (valid_append group15_expected_valid (valid_append group16_expected_valid (valid_append group17_expected_valid (valid_append group18_expected_valid (valid_append group19_expected_valid (valid_append group20_expected_valid (valid_append group21_expected_valid (valid_append group22_expected_valid (valid_append group23_expected_valid (valid_append group24_expected_valid (valid_append group25_expected_valid (valid_append group26_expected_valid (valid_append group27_expected_valid (valid_append group28_expected_valid (valid_append group29_expected_valid (valid_append group30_expected_valid (valid_append group31_expected_valid (valid_append group32_expected_valid (valid_append group33_expected_valid (valid_append group34_expected_valid group35_expected_valid)))))))))))))))))))))))))))))))))))
theorem hres_closed {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ResidualBound x y := by
  obtain ⟨c,hc,hxy⟩ := expected_cover hx hy
  exact allValid c hc x y hxy
theorem hres (x y : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) 1) (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    |-PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y
      -PoissonR3.forcing x y| ≤ PoissonR3.certR :=
  hres_closed ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩
#check allValid
#check hres_closed
#check hres
#print axioms allValid
#print axioms hres_closed
#print axioms hres
end PinnCertFarm
