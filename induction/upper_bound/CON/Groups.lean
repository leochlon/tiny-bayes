import Mathlib
import CON.Data
import CON.Clique

/-! Group numbers and positions of tokens (read from the table `slotTab`), and the per-group search test. -/

namespace CON

/-- The 16-bit field of `slotTab` for token `t`: `64 c + i`. -/
def slot (t : ℕ) : ℕ := (slotTab >>> (16 * t)) % 65536

/-- The group number of a token. -/
def cls (t : ℕ) : ℕ := slot t / 64 % numGroups

/-- The position of a token in its group. -/
def posOf (t : ℕ) : ℕ := slot t % 64

theorem cls_lt (a : ℕ) : cls a < numGroups := Nat.mod_lt _ (by decide)

/-- The search over the positions of group `c` stays within `caps3[c]`. -/
def classOK (c : ℕ) : Bool :=
  decide (mx (freeMasks.getD c 0) (groups.getD c []).length [] ≤ caps3.getD c 0)

end CON
