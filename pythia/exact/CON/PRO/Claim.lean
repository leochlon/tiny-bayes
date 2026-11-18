import Mathlib
import CON.PRO.Model

/-! # The claim "the tiny-transformer theorem extends to Pythia-14M", formally

The prompt `enc x` (`<|endoftext|>`, then ` red,` for `true` and ` blue,` for `false`) and the
prediction `p x = P(red) / (P(red) + P(blue))` for the next token are defined in `PRO.Model`.

* `avg q n k`: uniform average of `q` over the `C(n,k)` orderings of the bag `(n, k)`.
* `BayesInExpectation q ref N ε`: on every bag with `n ≤ N`, `|avg q n k - ref n k| ≤ ε`.
* `TinyTheorem q N ε ε' Δ`: the statement of the tiny-transformer theorem for a predictor `q`.
* `tbl`, `TableHolds`, `tiny_of_table`: the order averages in ten-thousandths and what follows from
  them. -/

namespace CON.PRO

open MeasureTheory

noncomputable section

/-- Uniform average of `q` over the orderings of the bag with `n` observations, `k` of them `true`. -/
def avg (q : List Bool → ℝ) (n k : ℕ) : ℝ :=
  (1 / (n.choose k : ℝ)) *
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k), q (List.ofFn x)

/-- Laplace's rule, the posterior predictive of the uniform prior. -/
def laplace (n k : ℕ) : ℝ := ((k : ℝ) + 1) / ((n : ℝ) + 2)

/-- The posterior predictive of the `Beta(a, b)` prior. -/
def betaRule (a b : ℝ) (n k : ℕ) : ℝ := ((k : ℝ) + a) / ((n : ℝ) + a + b)

/-- Bayesian in expectation: on every bag with `n ≤ N` the order average is within `ε` of `ref`. -/
def BayesInExpectation (q : List Bool → ℝ) (ref : ℕ → ℕ → ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, n ≤ N → k ≤ n → |avg q n k - ref n k| ≤ ε

/-- Likelihood of the sequence `x` under i.i.d. Bernoulli(`θ`) observations. -/
def bernLik (θ : ℝ) (x : List Bool) : ℝ := (x.map fun b => if b then θ else 1 - θ).prod

/-- Posterior predictive `P(next = 1 | x)` of the Bernoulli model under a prior `μ` on `θ`. -/
def postPred (μ : Measure ℝ) (x : List Bool) : ℝ :=
  (∫ θ, θ * bernLik θ x ∂μ) / ∫ θ, bernLik θ x ∂μ

/-- The tiny-transformer theorem, stated for a predictor `q`: Bayesian in expectation on the bags
with `n ≤ N` (within `ε` of Laplace's rule and within `ε'` of the `Beta(2, 9/4)` predictive), not
Bayesian in realization (two orderings of one bag at least `Δ` apart), hence not a function of the
bag, equal to no exchangeable predictor, the posterior predictive of no prior, and at least `Δ / 2`
away from every posterior predictive at some prompt. -/
def TinyTheorem (q : List Bool → ℝ) (N : ℕ) (ε ε' Δ : ℝ) : Prop :=
  BayesInExpectation q laplace N ε ∧
  BayesInExpectation q (betaRule 2 (9 / 4)) N ε' ∧
  (∃ x x' : List Bool, x.Perm x' ∧ q x ≠ q x' ∧ Δ ≤ |q x - q x'|) ∧
  (¬ ∃ f : ℕ → ℕ → ℝ, ∀ x : List Bool, q x = f x.length (x.count true)) ∧
  (∀ r : List Bool → ℝ, (∀ x x' : List Bool, x.Perm x' → r x = r x') → q ≠ r) ∧
  (∀ μ : Measure ℝ, q ≠ postPred μ) ∧
  (∀ μ : Measure ℝ, ∃ x : List Bool, Δ / 2 ≤ |q x - postPred μ x|)

end

/-! ## From an order gap to the corollaries (any predictor) -/

theorem bernLik_perm {x x' : List Bool} (h : x.Perm x') (θ : ℝ) : bernLik θ x = bernLik θ x' :=
  (h.map _).prod_eq

theorem postPred_perm (μ : Measure ℝ) {x x' : List Bool} (h : x.Perm x') :
    postPred μ x = postPred μ x' := by
  simp only [postPred, bernLik_perm h]

/-- A predictor that agrees on `x` and `x'` is at least half the order gap from `q` at one of them. -/
theorem half_gap {q r : List Bool → ℝ} {x x' : List Bool} {Δ : ℝ} (hr : r x = r x')
    (hΔ : Δ ≤ |q x - q x'|) : Δ / 2 ≤ |q x - r x| ∨ Δ / 2 ≤ |q x' - r x'| := by
  by_contra h
  push_neg at h
  have h1 : |q x - q x'| ≤ |q x - r x| + |r x - q x'| := abs_sub_le _ _ _
  have h2 : |r x - q x'| = |q x' - r x'| := by rw [hr, abs_sub_comm]
  rw [h2] at h1
  linarith [h.1, h.2]

/-- The corollaries of one order gap `Δ > 0`. -/
theorem corollaries_of_gap {q : List Bool → ℝ} {x x' : List Bool} {Δ : ℝ} (hperm : x.Perm x')
    (hpos : 0 < Δ) (hΔ : Δ ≤ |q x - q x'|) :
    (∃ x x' : List Bool, x.Perm x' ∧ q x ≠ q x' ∧ Δ ≤ |q x - q x'|) ∧
    (¬ ∃ f : ℕ → ℕ → ℝ, ∀ x : List Bool, q x = f x.length (x.count true)) ∧
    (∀ r : List Bool → ℝ, (∀ x x' : List Bool, x.Perm x' → r x = r x') → q ≠ r) ∧
    (∀ μ : Measure ℝ, q ≠ postPred μ) ∧
    (∀ μ : Measure ℝ, ∃ x : List Bool, Δ / 2 ≤ |q x - postPred μ x|) := by
  have hne : q x ≠ q x' := by
    intro h
    rw [h, sub_self, abs_zero] at hΔ
    linarith
  have hex : ∀ r : List Bool → ℝ, (∀ x x' : List Bool, x.Perm x' → r x = r x') → q ≠ r := by
    intro r hr h
    exact hne (by rw [h]; exact hr x x' hperm)
  refine ⟨⟨x, x', hperm, hne, hΔ⟩, ?_, hex, fun μ => hex _ fun _ _ h => postPred_perm μ h, ?_⟩
  · rintro ⟨f, hf⟩
    exact hne (by rw [hf, hf, hperm.length_eq, hperm.count_eq])
  · intro μ
    rcases half_gap (r := postPred μ) (postPred_perm μ hperm) hΔ with h | h
    · exact ⟨x, h⟩
    · exact ⟨x', h⟩

/-! ## From ten-thousandths to the tolerances -/

/-- If `v` is within `10^-4` of `c / 10^4` and the integers satisfy
`|c den - 10^4 num| ≤ (E - 1) den`, then `v` is within `E / 10^4` of `num / den`. -/
theorem close_of_table {v : ℝ} {c num den E : ℤ} (hden : 0 < den)
    (hv : |v - (c : ℝ) / 10000| ≤ 1 / 10000)
    (h1 : -((E - 1) * den) ≤ c * den - 10000 * num) (h2 : c * den - 10000 * num ≤ (E - 1) * den) :
    |v - (num : ℝ) / den| ≤ (E : ℝ) / 10000 := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have h1' : -(((E : ℝ) - 1) * den) ≤ (c : ℝ) * den - 10000 * num := by exact_mod_cast h1
  have h2' : (c : ℝ) * den - 10000 * num ≤ ((E : ℝ) - 1) * den := by exact_mod_cast h2
  have e : (c : ℝ) / 10000 - (num : ℝ) / den = ((c : ℝ) * den - 10000 * num) / (10000 * den) := by
    field_simp
  have hpos : (0 : ℝ) < 10000 * den := by positivity
  have h3 : |(c : ℝ) / 10000 - (num : ℝ) / den| ≤ ((E : ℝ) - 1) / 10000 := by
    rw [e, abs_le]
    constructor
    · rw [le_div_iff₀ hpos]
      calc -(((E : ℝ) - 1) / 10000) * (10000 * den) = -(((E : ℝ) - 1) * den) := by ring
        _ ≤ (c : ℝ) * den - 10000 * num := h1'
    · rw [div_le_iff₀ hpos]
      calc (c : ℝ) * den - 10000 * num ≤ ((E : ℝ) - 1) * den := h2'
        _ = ((E : ℝ) - 1) / 10000 * (10000 * den) := by ring
  calc |v - (num : ℝ) / den| ≤ |v - (c : ℝ) / 10000| + |(c : ℝ) / 10000 - (num : ℝ) / den| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 10000 + ((E : ℝ) - 1) / 10000 := add_le_add hv h3
    _ = (E : ℝ) / 10000 := by ring

/-- Order averages of `p` in ten-thousandths (float64 evaluation of the Hugging Face model, rounded),
row `n`, column `k`. -/
def tbl : List (List ℤ) :=
  [[4077],
   [4330, 5239],
   [2970, 4940, 7056],
   [2830, 3969, 5671, 7461],
   [2758, 3667, 4802, 6249, 7883],
   [2566, 3437, 4363, 5474, 6785, 8245],
   [2515, 3306, 4084, 4979, 6018, 7185, 8440],
   [2477, 3179, 3841, 4579, 5423, 6374, 7418, 8540],
   [2358, 3006, 3605, 4261, 4999, 5828, 6741, 7723, 8745]]

def bagTable (n k : ℕ) : ℤ := (tbl.getD n []).getD k 0

/-- Every table entry is within `0.1429` of Laplace's rule `(k+1)/(n+2)`. -/
theorem table_laplace : ∀ n : ℕ, n ≤ 8 → ∀ k : ℕ, k ≤ n →
    -((1430 - 1) * ((n : ℤ) + 2)) ≤ bagTable n k * ((n : ℤ) + 2) - 10000 * ((k : ℤ) + 1) ∧
      bagTable n k * ((n : ℤ) + 2) - 10000 * ((k : ℤ) + 1) ≤ (1430 - 1) * ((n : ℤ) + 2) := by
  decide +kernel

/-- Every table entry is within `0.0729` of the `Beta(2, 9/4)` predictive `(4k+8)/(4n+17)`. -/
theorem table_beta : ∀ n : ℕ, n ≤ 8 → ∀ k : ℕ, k ≤ n →
    -((730 - 1) * (4 * (n : ℤ) + 17)) ≤ bagTable n k * (4 * (n : ℤ) + 17) - 10000 * (4 * (k : ℤ) + 8) ∧
      bagTable n k * (4 * (n : ℤ) + 17) - 10000 * (4 * (k : ℤ) + 8) ≤ (730 - 1) * (4 * (n : ℤ) + 17) := by
  decide +kernel

/-- Bag averages within `10^-4` of the table, on the bags with `n ≤ N`. -/
def TableHolds (q : List Bool → ℝ) (N : ℕ) : Prop :=
  ∀ n k : ℕ, n ≤ N → k ≤ n → |avg q n k - (bagTable n k : ℝ) / 10000| ≤ 1 / 10000

theorem bie_of_table {q : List Bool → ℝ} {N : ℕ} (hN : N ≤ 8) (h : TableHolds q N) :
    BayesInExpectation q laplace N (143 / 1000) ∧
      BayesInExpectation q (betaRule 2 (9 / 4)) N (73 / 1000) := by
  constructor
  · intro n k hn hk
    obtain ⟨t1, t2⟩ := table_laplace n (hn.trans hN) k hk
    have := close_of_table (v := avg q n k) (c := bagTable n k) (num := (k : ℤ) + 1)
      (den := (n : ℤ) + 2) (E := 1430) (by positivity) (h n k hn hk) t1 t2
    have e : laplace n k = (((k : ℤ) + 1 : ℤ) : ℝ) / (((n : ℤ) + 2 : ℤ) : ℝ) := by
      unfold laplace; push_cast; rfl
    rw [e]
    refine this.trans ?_
    norm_num
  · intro n k hn hk
    obtain ⟨t1, t2⟩ := table_beta n (hn.trans hN) k hk
    have := close_of_table (v := avg q n k) (c := bagTable n k) (num := 4 * (k : ℤ) + 8)
      (den := 4 * (n : ℤ) + 17) (E := 730) (by positivity) (h n k hn hk) t1 t2
    have e : betaRule 2 (9 / 4) n k = ((4 * (k : ℤ) + 8 : ℤ) : ℝ) / ((4 * (n : ℤ) + 17 : ℤ) : ℝ) := by
      unfold betaRule
      push_cast
      have h1 : ((n : ℝ) + 2 + 9 / 4) ≠ 0 := by positivity
      have h2 : (4 * (n : ℝ) + 17) ≠ 0 := by positivity
      rw [div_eq_div_iff h1 h2]
      ring
    rw [e]
    refine this.trans ?_
    norm_num

/-- The tiny-transformer theorem for `q` from the bag table and one order gap. -/
theorem tiny_of_table {q : List Bool → ℝ} {N : ℕ} (hN : N ≤ 8) (h : TableHolds q N)
    {x x' : List Bool} {Δ : ℝ} (hperm : x.Perm x') (hpos : 0 < Δ) (hΔ : Δ ≤ |q x - q x'|) :
    TinyTheorem q N (143 / 1000) (73 / 1000) Δ :=
  ⟨(bie_of_table hN h).1, (bie_of_table hN h).2, corollaries_of_gap hperm hpos hΔ⟩

end CON.PRO
