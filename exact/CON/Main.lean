import Mathlib
import CON.Model
import CON.Invariance
import CON.Bags
import CON.Pythia
import CON.Cert
import CON.Cert2
import CON.Answer
import CON.K.BosL0
import CON.K.BosH0
import CON.K.BosO0
import CON.K.BosL1
import CON.K.BosH1
import CON.K.BosO1
import CON.K.BosL2
import CON.K.BosH2
import CON.K.BosO2
import CON.K.BosL3
import CON.K.BosH3
import CON.K.BosO3
import CON.K.BosL4
import CON.K.BosH4
import CON.K.BosO4
import CON.K.BosL5
import CON.K.BosH5
import CON.K.BosO5
import CON.K.BosFin

/-! # The tiny-transformer result does not extend to pythia-14m -/

namespace CON

noncomputable section

/-- The prompt of a binary sequence: one token per symbol (`t0` for 0, `t1` for 1) and nothing else,
as pythia's tokenizer produces it (`add_bos_token = false`). -/
def enc (t0 t1 : ℕ) (xs : List Bool) : List ℕ := xs.map fun b => if b then t1 else t0

/-- A prediction read off the final hidden state at the last position by an arbitrary rule `r`. -/
def predWith (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) (xs : List Bool) : ℝ :=
  r (lastHidden θ (enc t0 t1 xs))

/-- Candidate-renormalised probability that the next token is `t1`, among the candidates `t0`, `t1`
(the analogue of the tiny model's `p`, whose output is a two-way choice). -/
def pred (θ : Params) (t0 t1 : ℕ) (xs : List Bool) : ℝ :=
  Real.exp (logit θ (enc t0 t1 xs) t1) /
    (Real.exp (logit θ (enc t0 t1 xs) t0) + Real.exp (logit θ (enc t0 t1 xs) t1))

/-- Native probability that the next token is `t1`: softmax over the vocabulary `0..V-1`. -/
def predRaw (θ : Params) (V t0 t1 : ℕ) (xs : List Bool) : ℝ :=
  Real.exp (logit θ (enc t0 t1 xs) t1) / ∑ t ∈ Finset.range V, Real.exp (logit θ (enc t0 t1 xs) t)

/-- `p` is within `ε` of the rule `f n k` on the order average of every bag with `1 ≤ n ≤ 8`. -/
def BayesInExpectationRef (p : List Bool → ℝ) (f : ℕ → ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, 1 ≤ n → n ≤ 8 → k ≤ n → |avg p n k - f n k| ≤ ε

/-- The statement of `TinyBayes.bayes_in_expectation` for a predictor `p` and tolerance `ε`: on every
bag with `1 ≤ n ≤ 8`, the order average is within `ε` of Laplace's rule `(k+1)/(n+2)`. (The empty
prompt `n = 0` is left out: without a BOS token it has no last position.) -/
def BayesInExpectation (p : List Bool → ℝ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, 1 ≤ n → n ≤ 8 → k ≤ n → |avg p n k - ((k : ℝ) + 1) / ((n : ℝ) + 2)| ≤ ε

/-- The statement of `TinyBayes.not_bayes_in_realization` for `p`. -/
def NotBayesInRealization (p : List Bool → ℝ) : Prop :=
  ∃ x x' : List Bool, x.Perm x' ∧ p x ≠ p x'

/-- "The tiny result extends to `p`": Bayesian in expectation with the tiny result's `ε = 0.0034`,
and not Bayesian in realization. -/
def Extends (p : List Bool → ℝ) : Prop :=
  BayesInExpectation p (34 / 10000) ∧ NotBayesInRealization p

/-- Posterior predictive of a Beta(`a`, `b`) prior after `k` ones in `n` tokens (Laplace: `a = b = 1`). -/
def betaRule (a b : ℝ) (n k : ℕ) : ℝ := ((k : ℝ) + a) / ((n : ℝ) + a + b)

/-- Likelihood of the sequence `x` under i.i.d. Bernoulli(`θ`) tokens (as in the tiny development). -/
def bernLik (θ : ℝ) (x : List Bool) : ℝ := (x.map fun b => if b then θ else 1 - θ).prod

/-- Posterior predictive `P(next = 1 | x)` under a prior `μ` on `θ` (as in the tiny development). -/
def postPred (μ : MeasureTheory.Measure ℝ) (x : List Bool) : ℝ :=
  (∫ θ, θ * bernLik θ x ∂μ) / ∫ θ, bernLik θ x ∂μ

/-- The posterior predictive of the prior `μ` as a rule of the bag `(n, k)`. -/
def priorRule (μ : MeasureTheory.Measure ℝ) (n k : ℕ) : ℝ :=
  postPred μ (List.replicate k true ++ List.replicate (n - k) false)

end

theorem enc_zeros (t0 t1 n : ℕ) : enc t0 t1 (List.replicate n false) = List.replicate n t0 := by
  simp [enc]

theorem enc_ones (t0 t1 n : ℕ) : enc t0 t1 (List.replicate n true) = List.replicate n t1 := by
  simp [enc]

/-- **Length-blindness.** For every parameter assignment `θ` and every token `t`: on the prompt that
repeats `t` `n ≥ 1` times, the final hidden state at the last position is that of the one-token
prompt. Every next-token prediction is a function of this state. -/
theorem length_blind (θ : Params) (t n : ℕ) (hn : 1 ≤ n) :
    lastHidden θ (List.replicate n t) = lastHidden θ [t] :=
  lastHidden_replicate θ t n hn

/-- The order average on the bag of `n` zeros does not depend on `n`, whatever is read off. -/
theorem avg_zeros_const (θ : Params) (r : List ℝ → ℝ) (t0 t1 n : ℕ) (hn : 1 ≤ n) :
    avg (predWith θ r t0 t1) n 0 = r (lastHidden θ [t0]) := by
  rw [avg_zero]
  unfold predWith
  rw [enc_zeros, lastHidden_replicate θ t0 n hn]

/-- The order average on the bag of `n` ones does not depend on `n`, whatever is read off. -/
theorem avg_ones_const (θ : Params) (r : List ℝ → ℝ) (t0 t1 n : ℕ) (hn : 1 ≤ n) :
    avg (predWith θ r t0 t1) n n = r (lastHidden θ [t1]) := by
  rw [avg_full]
  unfold predWith
  rw [enc_ones, lastHidden_replicate θ t1 n hn]

/-- **Any reference must be flat.** If the order averages are within `ε` of a rule `f n k`, then `f`
moves by at most `2ε` along the all-zeros bags and along the all-ones bags. -/
theorem flat_reference (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) (f : ℕ → ℕ → ℝ) (ε : ℝ)
    (h : BayesInExpectationRef (predWith θ r t0 t1) f ε) (n m : ℕ) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hm : 1 ≤ m) (hm8 : m ≤ 8) : |f n 0 - f m 0| ≤ 2 * ε ∧ |f n n - f m m| ≤ 2 * ε := by
  have a1 := abs_le.mp (h n 0 hn hn8 (Nat.zero_le n))
  have a2 := abs_le.mp (h m 0 hm hm8 (Nat.zero_le m))
  have b1 := abs_le.mp (h n n hn hn8 le_rfl)
  have b2 := abs_le.mp (h m m hm hm8 le_rfl)
  rw [avg_zeros_const θ r t0 t1 n hn] at a1
  rw [avg_zeros_const θ r t0 t1 m hm] at a2
  rw [avg_ones_const θ r t0 t1 n hn] at b1
  rw [avg_ones_const θ r t0 t1 m hm] at b2
  constructor
  · rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · rw [abs_le]; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- **Every prior.** If the order averages are within `ε` of the posterior predictive of a prior `μ`
(any measure on `ℝ`), then that prior does not learn from a run of equal tokens: its predictive after
eight zeros is within `2ε` of its predictive after one zero, and likewise for ones. -/
theorem prior_must_not_learn (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) (μ : MeasureTheory.Measure ℝ)
    (ε : ℝ) (h : BayesInExpectationRef (predWith θ r t0 t1) (priorRule μ) ε) :
    |postPred μ [false] - postPred μ (List.replicate 8 false)| ≤ 2 * ε ∧
      |postPred μ [true] - postPred μ (List.replicate 8 true)| ≤ 2 * ε :=
  flat_reference θ r t0 t1 (priorRule μ) ε h 1 8 le_rfl (by norm_num) (by norm_num) le_rfl

/-- **Beta priors.** If the order averages are within `ε = 0.0034` of the posterior predictive
`(k + a) / (n + a + b)` of a Beta(`a`, `b`) prior, the prior is degenerate: `a + b ≤ 0.016` (the mass
sits at the endpoints) or `a + b ≥ 500` (eight observations barely move it). Laplace is `a = b = 1`. -/
theorem beta_degenerate (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : BayesInExpectationRef (predWith θ r t0 t1) (betaRule a b) (34 / 10000)) :
    a + b ≤ 16 / 1000 ∨ 500 ≤ a + b := by
  obtain ⟨h0, h1⟩ := flat_reference θ r t0 t1 (betaRule a b) (34 / 10000) h 1 8 le_rfl (by norm_num)
    (by norm_num) le_rfl
  have p1 : (0 : ℝ) < 1 + a + b := by linarith
  have p8 : (0 : ℝ) < 8 + a + b := by linarith
  have e0 : betaRule a b 1 0 - betaRule a b 8 0 = 7 * a / ((1 + a + b) * (8 + a + b)) := by
    simp only [betaRule]
    push_cast
    field_simp
    ring
  have e1 : betaRule a b 1 1 - betaRule a b 8 8 = -(7 * b) / ((1 + a + b) * (8 + a + b)) := by
    simp only [betaRule]
    push_cast
    field_simp
    ring
  rw [e0] at h0
  rw [e1] at h1
  have k0 := (abs_le.mp h0).2
  have k1 := (abs_le.mp h1).1
  rw [div_le_iff₀ (mul_pos p1 p8)] at k0
  rw [le_div_iff₀ (mul_pos p1 p8)] at k1
  by_contra hc
  push_neg at hc
  obtain ⟨c1, c2⟩ := hc
  nlinarith [mul_pos (sub_pos.mpr c1) (sub_pos.mpr c2)]

/-- **Not Bayesian in expectation, for any readout.** For every parameter assignment, every pair of
tokens, every rule `r` reading the prediction off the final hidden state, and every `ε < 7/60`, the
order averages are not within `ε` of Laplace's rule on the bags with `1 ≤ n ≤ 8`. -/
theorem not_bayes_in_expectation_with (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) (ε : ℝ)
    (hε : ε < 7 / 60) : ¬ BayesInExpectation (predWith θ r t0 t1) ε := by
  intro h
  have h1 := abs_le.mp (h 1 0 le_rfl (by norm_num) (by norm_num))
  have h8 := abs_le.mp (h 8 0 (by norm_num) le_rfl (by norm_num))
  rw [avg_zeros_const θ r t0 t1 1 le_rfl] at h1
  rw [avg_zeros_const θ r t0 t1 8 (by norm_num)] at h8
  have e1 : (((0 : ℕ) : ℝ) + 1) / (((1 : ℕ) : ℝ) + 2) = 1 / 3 := by norm_num
  have e8 : (((0 : ℕ) : ℝ) + 1) / (((8 : ℕ) : ℝ) + 2) = 1 / 10 := by norm_num
  rw [e1] at h1
  rw [e8] at h8
  linarith [h1.1, h8.2]

theorem pred_eq (θ : Params) (t0 t1 : ℕ) :
    pred θ t0 t1 = predWith θ (fun y => Real.exp (dot (θ.unemb t1) y) /
      (Real.exp (dot (θ.unemb t0) y) + Real.exp (dot (θ.unemb t1) y))) t0 t1 := rfl

theorem predRaw_eq (θ : Params) (V t0 t1 : ℕ) :
    predRaw θ V t0 t1 = predWith θ (fun y => Real.exp (dot (θ.unemb t1) y) /
      ∑ t ∈ Finset.range V, Real.exp (dot (θ.unemb t) y)) t0 t1 := rfl

/-- The candidate-renormalised prediction is not Bayesian in expectation for any `ε < 7/60 ≈ 0.1167`. -/
theorem not_bayes_in_expectation (θ : Params) (t0 t1 : ℕ) (ε : ℝ) (hε : ε < 7 / 60) :
    ¬ BayesInExpectation (pred θ t0 t1) ε := by
  rw [pred_eq]
  exact not_bayes_in_expectation_with θ _ t0 t1 ε hε

/-- Nor is the native next-token probability, for any vocabulary size. -/
theorem not_bayes_in_expectation_raw (θ : Params) (V t0 t1 : ℕ) (ε : ℝ) (hε : ε < 7 / 60) :
    ¬ BayesInExpectation (predRaw θ V t0 t1) ε := by
  rw [predRaw_eq]
  exact not_bayes_in_expectation_with θ _ t0 t1 ε hε

/-- **Faithfulness of `Extends`.** `Extends` asks no more than the tiny result states: a predictor
that satisfies the statements of `TinyBayes.bayes_in_expectation` and
`TinyBayes.not_bayes_in_realization` (copied here with `p` abstract) satisfies `Extends`. So the tiny
transformer satisfies `Extends`, and pythia-14m does not. -/
theorem extends_of_tiny_statements (p : List Bool → ℝ)
    (h1 : ∀ (n k : ℕ), n ≤ 8 → k ≤ n →
      |(1 / (n.choose k : ℝ)) * ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k),
        p (List.ofFn x) - ((k : ℝ) + 1) / ((n : ℝ) + 2)| ≤ 34 / 10000)
    (h2 : ∃ x x' : List Bool, x.Perm x' ∧ p x ≠ p x' ∧ (97412682 : ℝ) / 10 ^ 10 ≤ |p x - p x'|) :
    Extends p := by
  refine ⟨fun n k _ hn hk => h1 n k hn hk, ?_⟩
  obtain ⟨x, x', hp, hne, -⟩ := h2
  exact ⟨x, x', hp, hne⟩

/-- The same for every parameter assignment of the architecture: the obstruction is rotary position
embedding, which gives a repeated token no way to count its repetitions. -/
theorem main_all_params (θ : Params) (t0 t1 : ℕ) : ¬ Extends (pred θ t0 t1) := fun h =>
  not_bayes_in_expectation θ t0 t1 (34 / 10000) (by norm_num) h.1

/-- **Main result.** The tiny result does not extend to pythia-14m: for every pair of tokens `t0`, `t1`
standing for 0 and 1 (for instance `17`, `18`, the tokens "0", "1", or `470`, `337`, the tokens " 0",
" 1"), the candidate-renormalised next-token prediction of pythia-14m is not Bayesian in expectation
with `ε = 0.0034`, so the conjunction `Extends` fails. -/
theorem main (t0 t1 : ℕ) : ¬ Extends (pred pythia14m t0 t1) :=
  main_all_params pythia14m t0 t1

/-! ## With a BOS token: certified evaluation of the empty bag -/

noncomputable section

/-- The prompt with a leading BOS token (`<|endoftext|>`, token 0), as in the tiny model's `[BOS, x1..xn]`. -/
def encB (t0 t1 : ℕ) (xs : List Bool) : List ℕ := 0 :: enc t0 t1 xs

/-- Candidate-renormalised probability of `t1` against `t0` after the BOS-prefixed prompt. -/
def predB (θ : Params) (t0 t1 : ℕ) (xs : List Bool) : ℝ :=
  Real.exp (logit θ (encB t0 t1 xs) t1) /
    (Real.exp (logit θ (encB t0 t1 xs) t0) + Real.exp (logit θ (encB t0 t1 xs) t1))

/-- The statement of `TinyBayes.bayes_in_expectation` with its own bags, `n ≤ 8` including `n = 0`. -/
def BayesInExpectation0 (p : List Bool → ℝ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, n ≤ 8 → k ≤ n → |avg p n k - ((k : ℝ) + 1) / ((n : ℝ) + 2)| ≤ ε

/-- "The tiny result extends to `p`", with the empty bag included. -/
def Extends0 (p : List Bool → ℝ) : Prop :=
  BayesInExpectation0 p (34 / 10000) ∧ NotBayesInRealization p

end

/-- **Certified value.** After the prompt `[BOS]`, pythia-14m's two-way probability of "1" (token 18)
against "0" (token 17) is `0.98068…`; Laplace's rule gives `1/2`. -/
theorem bos_empty_17_18 : (980688 : ℝ) / 10 ^ 6 ≤ predB pythia14m 17 18 [] ∧
    predB pythia14m 17 18 [] ≤ (980689 : ℝ) / 10 ^ 6 := by
  have h := pred1_encl 0 17 18 Bos.B1 Bos.B2 Bos.B3 Bos.B4 Bos.B5 Bos.B6
    Bos.A0 Bos.A1 Bos.A2 Bos.A3 Bos.A4 Bos.A5 Bos.H0 Bos.H1 Bos.H2 Bos.H3 Bos.H4 Bos.H5 980688 980689
    Bos.a0 Bos.g0 Bos.o0 Bos.a1 Bos.g1 Bos.o1 Bos.a2 Bos.g2 Bos.o2 Bos.a3 Bos.g3 Bos.o3
    Bos.a4 Bos.g4 Bos.o4 Bos.a5 Bos.g5 Bos.o5 Bos.fin_17_18
  simp only [Int.cast_ofNat] at h
  exact h

/-- **Certified value.** The same for " 1" (token 337) against " 0" (token 470): `0.91242…`. -/
theorem bos_empty_470_337 : (912424 : ℝ) / 10 ^ 6 ≤ predB pythia14m 470 337 [] ∧
    predB pythia14m 470 337 [] ≤ (912426 : ℝ) / 10 ^ 6 := by
  have h := pred1_encl 0 470 337 Bos.B1 Bos.B2 Bos.B3 Bos.B4 Bos.B5 Bos.B6
    Bos.A0 Bos.A1 Bos.A2 Bos.A3 Bos.A4 Bos.A5 Bos.H0 Bos.H1 Bos.H2 Bos.H3 Bos.H4 Bos.H5 912424 912426
    Bos.a0 Bos.g0 Bos.o0 Bos.a1 Bos.g1 Bos.o1 Bos.a2 Bos.g2 Bos.o2 Bos.a3 Bos.g3 Bos.o3
    Bos.a4 Bos.g4 Bos.o4 Bos.a5 Bos.g5 Bos.o5 Bos.fin_470_337
  simp only [Int.cast_ofNat] at h
  exact h

/-- With a BOS token and the tokens "0", "1": not Bayesian in expectation for any `ε < 0.48`. -/
theorem not_bayes_bos_17_18 (ε : ℝ) (hε : ε < 48 / 100) :
    ¬ BayesInExpectation0 (predB pythia14m 17 18) ε := by
  intro h
  have h0 := abs_le.mp (h 0 0 (by norm_num) le_rfl)
  rw [avg_zero] at h0
  have e : (((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 2) = 1 / 2 := by norm_num
  rw [e] at h0
  have e2 : predB pythia14m 17 18 (List.replicate 0 false) = predB pythia14m 17 18 [] := rfl
  rw [e2] at h0
  have b := bos_empty_17_18.1
  have b' : (98 : ℝ) / 100 ≤ predB pythia14m 17 18 [] := le_trans (by norm_num) b
  linarith [h0.2]

/-- With a BOS token and the tokens " 0", " 1": not Bayesian in expectation for any `ε < 0.41`. -/
theorem not_bayes_bos_470_337 (ε : ℝ) (hε : ε < 41 / 100) :
    ¬ BayesInExpectation0 (predB pythia14m 470 337) ε := by
  intro h
  have h0 := abs_le.mp (h 0 0 (by norm_num) le_rfl)
  rw [avg_zero] at h0
  have e : (((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 2) = 1 / 2 := by norm_num
  rw [e] at h0
  have e2 : predB pythia14m 470 337 (List.replicate 0 false) = predB pythia14m 470 337 [] := rfl
  rw [e2] at h0
  have b := bos_empty_470_337.1
  have b' : (91 : ℝ) / 100 ≤ predB pythia14m 470 337 [] := le_trans (by norm_num) b
  linarith [h0.2]

/-- **With BOS.** The tiny result does not extend to pythia-14m under the BOS-prefixed encoding either,
for the digit tokens with or without a leading space. -/
theorem main_bos : ¬ Extends0 (predB pythia14m 17 18) ∧ ¬ Extends0 (predB pythia14m 470 337) :=
  ⟨fun h => not_bayes_bos_17_18 (34 / 10000) (by norm_num) h.1,
   fun h => not_bayes_bos_470_337 (34 / 10000) (by norm_num) h.1⟩


/-! ## The native prompt with certified values -/

/-! ## The red/blue prompt at the empty bag, evaluated in the kernel -/

/-- The red/blue prediction with `pythia14m`: ` red` (2502) against ` blue` (4797) after the prompt `PRO.enc x`
(`<|endoftext|>`, then ` red,` or ` blue,` per observation). -/
noncomputable def predP (θ : Params) (xs : List Bool) : ℝ :=
  Real.exp (logit θ (PRO.enc xs) 2502) /
    (Real.exp (logit θ (PRO.enc xs) 4797) + Real.exp (logit θ (PRO.enc xs) 2502))

/-- **Certified.** At the empty bag the prediction is `0.40769`, the table entry `0.4077` of `PRO.tbl`, here
evaluated in the kernel. Laplace's rule says 1/2. -/
theorem pro_empty_bag : (407692 : ℝ) / 10 ^ 6 ≤ predP pythia14m [] ∧
    predP pythia14m [] ≤ (407694 : ℝ) / 10 ^ 6 := by
  have h := pred1_encl 0 4797 2502 Bos.B1 Bos.B2 Bos.B3 Bos.B4 Bos.B5 Bos.B6
    Bos.A0 Bos.A1 Bos.A2 Bos.A3 Bos.A4 Bos.A5 Bos.H0 Bos.H1 Bos.H2 Bos.H3 Bos.H4 Bos.H5 407692 407694
    Bos.a0 Bos.g0 Bos.o0 Bos.a1 Bos.g1 Bos.o1 Bos.a2 Bos.g2 Bos.o2 Bos.a3 Bos.g3 Bos.o3 Bos.a4 Bos.g4 Bos.o4 Bos.a5 Bos.g5 Bos.o5 Bos.fin_4797_2502
  simp only [Int.cast_ofNat] at h
  exact h

/-- The kernel value agrees with `PRO.tbl` at the bag `(0, 0)` to `10^-4`. -/
theorem pro_table_entry_confirmed :
    |predP pythia14m [] - ((PRO.bagTable 0 0 : ℤ) : ℝ) / 10000| ≤ 1 / 10000 := by
  have e : ((PRO.bagTable 0 0 : ℤ) : ℝ) = 4077 := by
    have : PRO.bagTable 0 0 = 4077 := by decide
    rw [this]
    norm_num
  rw [e, abs_le]
  have h := pro_empty_bag
  constructor <;> linarith [h.1, h.2]

/-- Under the red/blue encoding the empty bag already misses the tiny tolerance: every `ε < 0.092`. -/
theorem pro_encoding_fails_tiny (ε : ℝ) (hε : ε < 92 / 1000) :
    ¬ BayesInExpectation0 (predP pythia14m) ε := by
  intro h
  have h0 := abs_le.mp (h 0 0 (by norm_num) le_rfl)
  rw [avg_zero] at h0
  have e : (((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 2) = 1 / 2 := by norm_num
  rw [e] at h0
  have e2 : predP pythia14m (List.replicate 0 false) = predP pythia14m [] := rfl
  rw [e2] at h0
  have b := pro_empty_bag.2
  have b' : predP pythia14m [] ≤ (408 : ℝ) / 1000 := le_trans b (by norm_num)
  linarith [h0.1]

/-- **Certified native mass.** After `<|endoftext|>` the native probabilities of
` red` and ` blue` sum to less than `3 · 10^-7`: the renormalised prediction `0.4077` is a ratio of two
events of negligible probability. -/
theorem pro_candidates_native_mass :
    native1 pythia14m 50304 0 2502 + native1 pythia14m 50304 0 4797 ≤ 3 / 10 ^ 7 := by
  have hx := resid_encl 0 Bos.B1 Bos.B2 Bos.B3 Bos.B4 Bos.B5 Bos.B6
    Bos.A0 Bos.A1 Bos.A2 Bos.A3 Bos.A4 Bos.A5 Bos.H0 Bos.H1 Bos.H2 Bos.H3 Bos.H4 Bos.H5
    Bos.a0 Bos.g0 Bos.o0 Bos.a1 Bos.g1 Bos.o1 Bos.a2 Bos.g2 Bos.o2 Bos.a3 Bos.g3 Bos.o3 Bos.a4 Bos.g4 Bos.o4 Bos.a5 Bos.g5 Bos.o5
  have h1 := native1_encl 0 2502 50 (by norm_num) Bos.B6 116 hx Bos.mass_2502_50
  have h2 := native1_encl 0 4797 50 (by norm_num) Bos.B6 168 hx Bos.mass_4797_50
  simp only [Int.cast_ofNat] at h1 h2
  have e : (116 : ℝ) / 10 ^ 9 + 168 / 10 ^ 9 ≤ 3 / 10 ^ 7 := by norm_num
  linarith

/-- **Certified.** After `<|endoftext|>` the native probability of "1" (token 18) is at most `0.142`. -/
theorem bos_one_native_mass : native1 pythia14m 50304 0 18 ≤ 142 / 1000 := by
  have hx := resid_encl 0 Bos.B1 Bos.B2 Bos.B3 Bos.B4 Bos.B5 Bos.B6
    Bos.A0 Bos.A1 Bos.A2 Bos.A3 Bos.A4 Bos.A5 Bos.H0 Bos.H1 Bos.H2 Bos.H3 Bos.H4 Bos.H5
    Bos.a0 Bos.g0 Bos.o0 Bos.a1 Bos.g1 Bos.o1 Bos.a2 Bos.g2 Bos.o2 Bos.a3 Bos.g3 Bos.o3 Bos.a4 Bos.g4 Bos.o4 Bos.a5 Bos.g5 Bos.o5
  have h1 := native1_encl 0 18 50 (by norm_num) Bos.B6 141285996 hx Bos.mass_18_50
  simp only [Int.cast_ofNat] at h1
  exact le_trans h1 (by norm_num)

/-! ## `PRO.TinyTheorem` at its tolerances, on the digit prompts -/

/-- **... and with a BOS token.** It also fails for the BOS-prefixed digit prompts, at the empty bag:
`0.981` and `0.912` against `1/2`. -/
theorem pro_theorem_fails_bos_digits (Δ : ℝ) :
    ¬ PRO.TinyTheorem (predB pythia14m 17 18) 8 (143 / 1000) (73 / 1000) Δ ∧
      ¬ PRO.TinyTheorem (predB pythia14m 470 337) 8 (143 / 1000) (73 / 1000) Δ := by
  have e2 : PRO.laplace 0 0 = 1 / 2 := by
    unfold PRO.laplace
    norm_num
  constructor
  · intro h
    have h0 := abs_le.mp (h.1 0 0 (by norm_num) le_rfl)
    have e1 : PRO.avg (predB pythia14m 17 18) 0 0 = avg (predB pythia14m 17 18) 0 0 := rfl
    rw [e1, avg_zero, e2] at h0
    have e3 : predB pythia14m 17 18 (List.replicate 0 false) = predB pythia14m 17 18 [] := rfl
    rw [e3] at h0
    have b' : (98 : ℝ) / 100 ≤ predB pythia14m 17 18 [] := le_trans (by norm_num) bos_empty_17_18.1
    linarith [h0.2]
  · intro h
    have h0 := abs_le.mp (h.1 0 0 (by norm_num) le_rfl)
    have e1 : PRO.avg (predB pythia14m 470 337) 0 0 = avg (predB pythia14m 470 337) 0 0 := rfl
    rw [e1, avg_zero, e2] at h0
    have e3 : predB pythia14m 470 337 (List.replicate 0 false) = predB pythia14m 470 337 [] := rfl
    rw [e3] at h0
    have b' : (91 : ℝ) / 100 ≤ predB pythia14m 470 337 [] := le_trans (by norm_num) bos_empty_470_337.1
    linarith [h0.2]

/-- The Beta(2, 9/4) rule at tolerance `0.073` fails on the native prompt for every token
pair, readout and parameter assignment: the rule moves by `0.218` between one zero and eight zeros. -/
theorem pro_beta_fails_native (θ : Params) (r : List ℝ → ℝ) (t0 t1 : ℕ) :
    ¬ BayesInExpectationRef (predWith θ r t0 t1) (PRO.betaRule 2 (9 / 4)) (73 / 1000) := by
  intro h
  have hf := (flat_reference θ r t0 t1 _ _ h 1 8 le_rfl (by norm_num) (by norm_num) le_rfl).1
  have e : PRO.betaRule 2 (9 / 4) 1 0 - PRO.betaRule 2 (9 / 4) 8 0 = 32 / 147 := by
    unfold PRO.betaRule
    norm_num
  rw [e] at hf
  norm_num [abs_le] at hf

/-! ## Consequences of `PRO.Cert8` (proofs in `CON.Answer`) -/

/-- **`Cert8` excludes the tiny statement.** `PRO.main` is `Cert8 → TinyTheorem p 8 0.143 0.073 0.52`.
The same `Cert8` implies that `p` is not Bayesian in expectation at the tiny result's `ε = 0.0034`. -/
theorem pro_hypothesis_refutes_tiny (h : PRO.Cert8) :
    ¬ PRO.BayesInExpectation PRO.p PRO.laplace 8 (34 / 10000) :=
  pro_cert_refutes_laplace h _ (by norm_num)

/-- ... and for every `ε < 0.1426`, 42 times the tiny tolerance. -/
theorem pro_hypothesis_refutes_laplace (h : PRO.Cert8) (ε : ℝ) (hε : ε < 1426 / 10000) :
    ¬ PRO.BayesInExpectation PRO.p PRO.laplace 8 ε :=
  pro_cert_refutes_laplace h ε hε

/-- **`Cert8` excludes every prior.** Under `Cert8`, `p` is not within `0.044` of the posterior
predictive of any prior on `[0, 1]`: 13 times the tiny tolerance, with the prior left free. -/
theorem pro_hypothesis_refutes_every_prior (h : PRO.Cert8) (μ : MeasureTheory.Measure ℝ)
    (hμ : IsPrior01 μ) : ¬ PRO.BayesInExpectation PRO.p (proPriorRule μ) 8 (44 / 1000) :=
  pro_cert_no_prior h μ hμ

/-- The same from the hypothesis of `PRO.main_small` (bags with `n ≤ 2`, 7 prompts). -/
theorem pro_small_hypothesis_refutes_every_prior (h : PRO.BagCerts 2) (μ : MeasureTheory.Measure ℝ)
    (hμ : IsPrior01 μ) : ¬ PRO.BayesInExpectation PRO.p (proPriorRule μ) 2 (44 / 1000) :=
  pro_small_cert_no_prior h μ hμ

/-- The same for any predictor whose order averages are `PRO.tbl` on the bags with `n ≤ 2`. -/
theorem pro_table_refutes_every_prior (q : List Bool → ℝ) (h : PRO.TableHolds q 2)
    (μ : MeasureTheory.Measure ℝ) (hμ : IsPrior01 μ) :
    ¬ PRO.BayesInExpectation q (proPriorRule μ) 2 (44 / 1000) :=
  pro_table_no_prior q h μ hμ


/-- **`PRO.TinyTheorem` admits a predictor that is not monotone in the evidence** (`CON.Answer`): `antiPred`
meets `PRO.TinyTheorem` with its constants, and its order average falls by more than `0.05` from the
bag `(8, 4)` to the bag `(8, 5)`. -/
theorem pro_criterion_admits_antimonotone :
    PRO.TinyTheorem antiPred 8 (143 / 1000) (73 / 1000) (52 / 100) ∧
      PRO.avg antiPred 8 5 + 5 / 100 < PRO.avg antiPred 8 4 :=
  pro_tolerances_admit_antimonotone

/-- At the tiny tolerance that cannot happen: the order average rises by more than `0.09` per extra one. -/
theorem tiny_criterion_forces_increase (q : List Bool → ℝ)
    (h : PRO.BayesInExpectation q PRO.laplace 8 (34 / 10000)) (n k : ℕ) (hn : n ≤ 8) (hk : k < n) :
    PRO.avg q n k + 9 / 100 < PRO.avg q n (k + 1) :=
  tiny_tolerance_forces_increase q h n k hn hk

end CON
