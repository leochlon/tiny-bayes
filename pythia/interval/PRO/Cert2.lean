import Mathlib
import PRO.Compose
import PRO.K.Fin_e
import PRO.K.C0_q0
import PRO.K.C0_a0
import PRO.K.C0_h0
import PRO.K.C0_o0
import PRO.K.C0_q1
import PRO.K.C0_a1
import PRO.K.C0_h1
import PRO.K.C0_o1
import PRO.K.C0_q2
import PRO.K.C0_a2
import PRO.K.C0_h2
import PRO.K.C0_o2
import PRO.K.C0_q3
import PRO.K.C0_a3
import PRO.K.C0_h3
import PRO.K.C0_o3
import PRO.K.C0_q4
import PRO.K.C0_a4
import PRO.K.C0_h4
import PRO.K.C0_o4
import PRO.K.C0_q5
import PRO.K.C0_a5
import PRO.K.C0_h5
import PRO.K.C0_o5

/-! # Certified enclosures of `p` on the seven prompts with at most two observations

Each `resid_*` chains the kernel checks of `PRO.K` through `layer_ok`; each `encl_*` is a ten-digit
enclosure of Pythia-14M's prediction `p`. -/

namespace PRO

theorem resid_e : List.Forall₂ (List.Forall₂ (memAt S))
    (layers.foldl (fun xs L => block L xs) ((enc []).map fun t => vec (embRow t) 128))
    [B.C0.X6] := by
  have he : enc [] = [0] := rfl
  rw [he, foldl_layers]
  have h0 : List.Forall₂ (List.Forall₂ (memAt S)) (([0] : List ℕ).map fun t => vec (embRow t) 128)
      [vecI (embRow 0) 128] :=
    f2_map_same (fun t => f2_vec (embRow t) 128) [0]
  have h1 := layer_ok1 (LL 0) h0 K.C0_q0 K.C0_a0 K.C0_h0 K.C0_o0
  have h2 := layer_ok1 (LL 1) h1 K.C0_q1 K.C0_a1 K.C0_h1 K.C0_o1
  have h3 := layer_ok1 (LL 2) h2 K.C0_q2 K.C0_a2 K.C0_h2 K.C0_o2
  have h4 := layer_ok1 (LL 3) h3 K.C0_q3 K.C0_a3 K.C0_h3 K.C0_o3
  have h5 := layer_ok1 (LL 4) h4 K.C0_q4 K.C0_a4 K.C0_h4 K.C0_o4
  have h6 := layer_ok1 (LL 5) h5 K.C0_q5 K.C0_a5 K.C0_h5 K.C0_o5
  exact h6

theorem encl_e : (4076930531 : ℝ) / 10 ^ 10 ≤ p [] ∧ p [] ≤ (4076930534 : ℝ) / 10 ^ 10 := by
  have h := p_encl_of_boxes resid_e K.fin_e
  simp only [Int.cast_ofNat] at h
  exact h

end PRO
