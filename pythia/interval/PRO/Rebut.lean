import Mathlib
import PRO.Claim
import PRO.Sound

/-! # The criterion `Con.Extends`

`Con.BayesInExpectation`, `Con.BayesInExpectation0`, `Con.NotBayesInRealization`, `Con.Extends`,
`Con.Extends0` restate the definitions of `CON.Main` in `exact/` (its `avg` is the same expression
as `PRO.avg`). `Con.Extends` fixes Laplace's rule and the tolerance `0.0034`.

* `con_rejects_exact_bayes`: the posterior predictive of the Jeffreys prior `Beta(1/2, 1/2)`, an
  exchangeable predictor whose order average is exactly a posterior predictive, fails
  `Con.BayesInExpectation` for every `ε < 1/12`. So `Con.Extends` does not test "Bayesian in
  expectation"; it tests agreement with the uniform prior.
* `con_extends_needs_uniform_prior`: no predictor whose order averages are exactly the Jeffreys
  posterior predictive satisfies `Con.Extends` or `Con.Extends0`, whatever its order gaps. -/

namespace PRO

namespace Con

/-- `BayesInExpectation` of `CON.Main`: within `ε` of Laplace's rule on the bags with `1 ≤ n ≤ 8`. -/
def BayesInExpectation (p : List Bool → ℝ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, 1 ≤ n → n ≤ 8 → k ≤ n → |avg p n k - ((k : ℝ) + 1) / ((n : ℝ) + 2)| ≤ ε

/-- `BayesInExpectation0` of `CON.Main`: the same with the empty bag. -/
def BayesInExpectation0 (p : List Bool → ℝ) (ε : ℝ) : Prop :=
  ∀ n k : ℕ, n ≤ 8 → k ≤ n → |avg p n k - ((k : ℝ) + 1) / ((n : ℝ) + 2)| ≤ ε

/-- `NotBayesInRealization` of `CON.Main`. -/
def NotBayesInRealization (p : List Bool → ℝ) : Prop :=
  ∃ x x' : List Bool, x.Perm x' ∧ p x ≠ p x'

/-- `Extends` of `CON.Main`: tolerance fixed at the tiny model's `0.0034`. -/
def Extends (p : List Bool → ℝ) : Prop :=
  BayesInExpectation p (34 / 10000) ∧ NotBayesInRealization p

/-- `Extends0` of `CON.Main`. -/
def Extends0 (p : List Bool → ℝ) : Prop :=
  BayesInExpectation0 p (34 / 10000) ∧ NotBayesInRealization p

end Con

/-- The order average of a constant predictor is that constant. -/
theorem avg_const (c : ℝ) {n k : ℕ} (hk : k ≤ n) : avg (fun _ => c) n k = c := by
  unfold avg
  rw [bag_sum (fun _ => c) n k]
  have hC : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, orderings_length]
  field_simp

/-- The order average of a function of the bag is that function. -/
theorem avg_bagfun (f : ℕ → ℕ → ℝ) {n k : ℕ} (hk : k ≤ n) :
    avg (fun x => f x.length (x.count true)) n k = f n k := by
  have h : avg (fun x => f x.length (x.count true)) n k = avg (fun _ => f n k) n k := by
    unfold avg
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    show f (List.ofFn x).length ((List.ofFn x).count true) = f n k
    rw [List.length_ofFn, (Finset.mem_filter.mp hx).2]
  rw [h, avg_const _ hk]

/-- The posterior predictive of the Jeffreys prior `Beta(1/2, 1/2)`: `(k + 1/2) / (n + 1)`. -/
noncomputable def jeffreys (x : List Bool) : ℝ := ((x.count true : ℝ) + 1 / 2) / ((x.length : ℝ) + 1)

theorem jeffreys_exchangeable (x x' : List Bool) (h : x.Perm x') : jeffreys x = jeffreys x' := by
  unfold jeffreys
  rw [h.count_eq, h.length_eq]

/-- Its order average on every bag is the `Beta(1/2, 1/2)` posterior predictive, exactly. -/
theorem jeffreys_avg {n k : ℕ} (hk : k ≤ n) : avg jeffreys n k = betaRule (1 / 2) (1 / 2) n k := by
  have h := avg_bagfun (fun (n k : ℕ) => ((k : ℝ) + 1 / 2) / ((n : ℝ) + 1)) hk
  have e : jeffreys = fun x => (fun (n k : ℕ) => ((k : ℝ) + 1 / 2) / ((n : ℝ) + 1)) x.length
      (x.count true) := rfl
  rw [e, h]
  unfold betaRule
  congr 1
  ring

/-- **`Con.BayesInExpectation` rejects an exactly Bayesian predictor.** A predictor whose order averages are
exactly the posterior predictive of the Jeffreys prior fails `Con.BayesInExpectation` for every
`ε < 1/12`: at the bag `(1, 1)` its average is `3/4`, Laplace's rule is `2/3`. -/
theorem con_rejects_of_jeffreys_avg (q : List Bool → ℝ)
    (hq : ∀ n k : ℕ, k ≤ n → avg q n k = betaRule (1 / 2) (1 / 2) n k) (ε : ℝ) (hε : ε < 1 / 12) :
    ¬ Con.BayesInExpectation q ε := by
  intro h
  have h1 := h 1 1 le_rfl (by norm_num) le_rfl
  rw [hq 1 1 le_rfl] at h1
  unfold betaRule at h1
  rw [abs_le] at h1
  obtain ⟨-, h2⟩ := h1
  norm_num at h2
  linarith

theorem con_rejects_exact_bayes :
    (∀ x x' : List Bool, x.Perm x' → jeffreys x = jeffreys x') ∧
    (∀ n k : ℕ, k ≤ n → avg jeffreys n k = betaRule (1 / 2) (1 / 2) n k) ∧
    ∀ ε : ℝ, ε < 1 / 12 → ¬ Con.BayesInExpectation jeffreys ε :=
  ⟨jeffreys_exchangeable, fun _ _ hk => jeffreys_avg hk,
    fun ε hε => con_rejects_of_jeffreys_avg jeffreys (fun _ _ hk => jeffreys_avg hk) ε hε⟩

/-- No predictor that is exactly Bayesian in expectation for the Jeffreys prior satisfies
`Con.Extends` or `Con.Extends0`, whatever its behaviour on single orderings. -/
theorem con_extends_needs_uniform_prior (q : List Bool → ℝ)
    (hq : ∀ n k : ℕ, k ≤ n → avg q n k = betaRule (1 / 2) (1 / 2) n k) :
    ¬ Con.Extends q ∧ ¬ Con.Extends0 q := by
  constructor
  · intro h
    exact con_rejects_of_jeffreys_avg q hq (34 / 10000) (by norm_num) h.1
  · intro h
    exact con_rejects_of_jeffreys_avg q hq (34 / 10000) (by norm_num)
      (fun n k _ hn hk => h.1 n k hn hk)

/-- No constant predictor is within `0.143` of Laplace's rule on the bags with `n ≤ 2` either. -/
theorem const_not_bayes2 (c : ℝ) : ¬ BayesInExpectation (fun _ => c) laplace 2 (143 / 1000) := by
  intro h
  have h0 := h 2 0 (le_refl 2) (by norm_num)
  have h2 := h 2 2 (le_refl 2) (le_refl 2)
  rw [avg_const c (by norm_num)] at h0 h2
  unfold laplace at h0 h2
  rw [abs_le] at h0 h2
  obtain ⟨-, a2⟩ := h0
  obtain ⟨b1, -⟩ := h2
  norm_num at a2 b1
  linarith

/-- **The criterion forces learning on one-colour prompts.** A predictor within `0.073` of the
`Beta(2, 9/4)` rule on the bags with `n ≤ 8` has order averages that move with the length of an
all-blue and of an all-red prompt. -/
theorem criterion_forces_learning (q : List Bool → ℝ)
    (h : BayesInExpectation q (betaRule 2 (9 / 4)) 8 (73 / 1000)) :
    avg q 8 0 + 7 / 100 ≤ avg q 1 0 ∧ avg q 1 1 + 9 / 100 ≤ avg q 8 8 := by
  obtain ⟨a1, a2⟩ := abs_le.mp (h 1 0 (by norm_num) (by norm_num))
  obtain ⟨b1, b2⟩ := abs_le.mp (h 8 0 (le_refl 8) (by norm_num))
  obtain ⟨c1, c2⟩ := abs_le.mp (h 1 1 (by norm_num) (le_refl 1))
  obtain ⟨d1, d2⟩ := abs_le.mp (h 8 8 (le_refl 8) (le_refl 8))
  unfold betaRule at a1 a2 b1 b2 c1 c2 d1 d2
  norm_num at a1 a2 b1 b2 c1 c2 d1 d2
  constructor <;> linarith

/-- So no predictor that is blind to the length of a one-colour prompt (as every predictor is under
the native encoding without BOS, by `CON.length_blind`) meets the criterion. -/
theorem length_blind_fails (q : List Bool → ℝ) (hq : avg q 1 0 = avg q 8 0) :
    ¬ BayesInExpectation q (betaRule 2 (9 / 4)) 8 (73 / 1000) := by
  intro h
  have h1 := (criterion_forces_learning q h).1
  linarith

end PRO
