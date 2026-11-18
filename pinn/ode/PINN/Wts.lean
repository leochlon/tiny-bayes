import PINN.WeightsN
import PINN.WeightsH

/-! The weight lists of both networks (integers over `2^16`), bundled. Core Lean only. -/

namespace PINN

/-- Integer weights of a 1 → 32 → 32 → 1 tanh network: `w1, c1` first layer, `w2` (row `j` = weights into
unit `j`), `c2` second layer, `w3, c3` output. Every real weight is the integer divided by `2^16`. -/
structure Wts where
  w1 : List Int
  c1 : List Int
  w2 : List (List Int)
  c2 : List Int
  w3 : List Int
  c3 : Int

/-- The weights of `N` (`data/net.json`). -/
def WN : Wts := ⟨NetW.W1, NetW.b1, NetW.W2, NetW.b2, NetW.W3, NetW.b3⟩

/-- The weights of `Ñ` (`data/net_hardic.json`). -/
def WH : Wts := ⟨NetH.W1, NetH.b1, NetH.W2, NetH.b2, NetH.W3, NetH.b3⟩

end PINN
