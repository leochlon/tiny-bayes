import OracleNumeric
import OracleIntervalSound
import StagedSound
namespace PinnOracle
open PinnCert
theorem envelope_sound (b : Cell) (c d : Oracle)
    (hc : c.Valid (cst b.cx) (cst b.cy)) (hd : d.Valid b.X b.Y)
    (h : envelope b c d = true) {x y : ℝ} (hb : b.Contains x y) :
    |-PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y
      -PoissonR3.forcing x y| ≤ PoissonR3.certR := by
  apply PinnStaged.check_sound b _ hb
  unfold envelope at h
  rw [outInterval0 c _ _ hc, outInterval1 c _ _ hc, outInterval2 c _ _ hc,
    outInterval3 d _ _ hd, outInterval4 d _ _ hd, outInterval5 d _ _ hd,
    outInterval6 d _ _ hd] at h
  exact h
#check envelope_sound
#print axioms envelope_sound
end PinnOracle
