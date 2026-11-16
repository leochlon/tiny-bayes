import Mathlib
import CON.Cert

/-! # One-token certificates, second part

* `resid6 t`: the residual stream of `pythia14m` after its six layers on the one-token prompt `[t]`;
  `resid_encl` puts it in a box from eighteen kernel checks.
* `native1`: the native (not renormalised) next-token probability after a one-token prompt, a softmax
  over the whole vocabulary; `native1_encl` bounds it from above by one competitor token, with a kernel
  check `massCheck` on the logit gap. -/

namespace CON

/-- The residual stream of `pythia14m` after the six layers on the one-token prompt `[t]`. -/
noncomputable def resid6 (t : ℕ) : List ℝ :=
  stepC z5.toLayer (stepC z4.toLayer (stepC z3.toLayer (stepC z2.toLayer (stepC z1.toLayer
    (stepC z0.toLayer (row 128 (eRowN t)))))))

theorem lastHidden_resid (t : ℕ) :
    lastHidden pythia14m [t] = layerNorm (row 128 W.lnfg) (row 128 W.lnfb) (resid6 t) := by
  rw [lastHidden_single]
  rfl

/-- Eighteen kernel checks (three per layer) put the residual stream in the box `B6`. -/
theorem resid_encl (t : ℕ) (B1 B2 B3 B4 B5 B6 A0 A1 A2 A3 A4 A5 H0 H1 H2 H3 H4 H5 : List Iv)
    (a0 : attCheck z0 (embI (eRowN t)) A0 = true) (g0 : hidCheck z0 (embI (eRowN t)) H0 = true)
    (o0 : outCheck z0 (embI (eRowN t)) A0 H0 B1 = true)
    (a1 : attCheck z1 B1 A1 = true) (g1 : hidCheck z1 B1 H1 = true) (o1 : outCheck z1 B1 A1 H1 B2 = true)
    (a2 : attCheck z2 B2 A2 = true) (g2 : hidCheck z2 B2 H2 = true) (o2 : outCheck z2 B2 A2 H2 B3 = true)
    (a3 : attCheck z3 B3 A3 = true) (g3 : hidCheck z3 B3 H3 = true) (o3 : outCheck z3 B3 A3 H3 B4 = true)
    (a4 : attCheck z4 B4 A4 = true) (g4 : hidCheck z4 B4 H4 = true) (o4 : outCheck z4 B4 A4 H4 B5 = true)
    (a5 : attCheck z5 B5 A5 = true) (g5 : hidCheck z5 B5 H5 = true) (o5 : outCheck z5 B5 A5 H5 B6 = true) :
    List.Forall₂ (memAt S) (resid6 t) B6 := by
  have e0 := f2_emb (eRowN t)
  have s1 := layer_ok3 z0 e0 a0 g0 o0
  have s2 := layer_ok3 z1 s1 a1 g1 o1
  have s3 := layer_ok3 z2 s2 a2 g2 o2
  have s4 := layer_ok3 z3 s3 a3 g3 o3
  have s5 := layer_ok3 z4 s4 a4 g4 o4
  exact layer_ok3 z5 s5 a5 g5 o5

/-- Native probability of the token `t` after the one-token prompt `[tok]`: softmax over the tokens
`0..V-1`. -/
noncomputable def native1 (θ : Params) (V tok t : ℕ) : ℝ :=
  Real.exp (logit θ [tok] t) / ∑ s ∈ Finset.range V, Real.exp (logit θ [tok] s)

/-- One competitor bounds the native probability: `P(t) ≤ exp (-(logit top - logit t))`. -/
theorem native1_le (θ : Params) (V tok t top : ℕ) (htop : top < V) :
    native1 θ V tok t ≤ Real.exp (-(logit θ [tok] top - logit θ [tok] t)) := by
  unfold native1
  have hsum : Real.exp (logit θ [tok] top) ≤ ∑ s ∈ Finset.range V, Real.exp (logit θ [tok] s) :=
    Finset.single_le_sum (f := fun s => Real.exp (logit θ [tok] s)) (fun s _ => (Real.exp_pos _).le)
      (Finset.mem_range.mpr htop)
  have hpos := Real.exp_pos (logit θ [tok] top)
  have e : Real.exp (-(logit θ [tok] top - logit θ [tok] t)) =
      Real.exp (logit θ [tok] t) / Real.exp (logit θ [tok] top) := by
    rw [neg_sub, Real.exp_sub]
  rw [e]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hsum

/-- Checks `exp (-(logit top - logit t)) ≤ hi / 10^9` from a box `B` for the residual stream after the
last layer (`ut`, `utop` the packed unembedding rows of `t` and of the competitor). -/
def massCheck (ut utop : Nat) (B : List Iv) (hi : Int) : Bool :=
  (expI (neg (logitDiffI W.lnfg W.lnfb ut utop B))).ok &&
    decide ((expI (neg (logitDiffI W.lnfg W.lnfb ut utop B))).hi * 1000000000 ≤ hi * S)

/-- **Native-mass certificate.** The native probability of `t` after `[tok]` is at most `hi / 10^9`. -/
theorem native1_encl (tok t top : ℕ) (htop : top < 50304) (B6 : List Iv) (hi : ℤ)
    (hx : List.Forall₂ (memAt S) (resid6 tok) B6)
    (hm : massCheck (uRowN t) (uRowN top) B6 hi = true) :
    native1 pythia14m 50304 tok t ≤ (hi : ℝ) / 10 ^ 9 := by
  refine le_trans (native1_le pythia14m 50304 tok t top htop) ?_
  have hd := memAt_exp (memAt_neg (memAt_logitDiff W.lnfg W.lnfb (uRowN t) (uRowN top) hx))
  have hl : logit pythia14m [tok] top - logit pythia14m [tok] t =
      dot (row 128 (uRowN top)) (layerNorm (row 128 W.lnfg) (row 128 W.lnfb) (resid6 tok)) -
        dot (row 128 (uRowN t)) (layerNorm (row 128 W.lnfg) (row 128 W.lnfb) (resid6 tok)) := by
    unfold logit
    rw [lastHidden_resid]
    rfl
  rw [hl]
  simp only [massCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨hok, c⟩ := hm
  obtain ⟨-, d2⟩ := hd hok
  have hS := S_pos
  have c' : ((expI (neg (logitDiffI W.lnfg W.lnfb (uRowN t) (uRowN top) B6))).hi : ℝ) * 1000000000 ≤
      (hi : ℝ) * S := by exact_mod_cast c
  rw [le_div_iff₀ (by norm_num)]
  apply le_of_mul_le_mul_right _ hS
  exact le_trans (le_of_eq (by ring))
    (le_trans (mul_le_mul_of_nonneg_right d2 (by norm_num : (0 : ℝ) ≤ 1000000000)) c')

end CON
