import Mathlib
import CON.PRO.Main

/-! # Consequences of the 45-bag table of `CON.PRO`

`CON.PRO.*` is an earlier version of the interval development (`interval/`), under the namespace
`CON.PRO`. Its `main` is conditional: `Cert8 → TinyTheorem p 8 0.143 0.073 0.52`, where `Cert8`
asserts that the order averages are within `10^-4` of the table `tbl`.

The theorems below take that hypothesis and that table and derive:

* `pro_table_refutes_laplace`: the order average on the bag `(1, 1)` is `0.5239` where Laplace's rule
  says `2/3`, so the criterion fails for every `ε < 0.1426`, in particular for the tiny result's `0.0034`.
* `pro_table_no_prior`: the three bags `(1,1)`, `(2,1)`, `(2,2)` are incompatible with the posterior
  predictive of every prior on `[0, 1]` at tolerance `0.044`: a posterior predictive `f` satisfies
  `f(1,1) = f(1,1) f(2,2) + (1 - f(1,1)) f(2,1)`, and the table violates this by a wide margin. -/

namespace CON

open MeasureTheory

/-- A prior on the unit interval: a finite measure concentrated on `[0, 1]` (every probability measure
on `[0, 1]` is one). -/
def IsPrior01 (μ : Measure ℝ) : Prop := IsFiniteMeasure μ ∧ ∀ᵐ θ ∂μ, θ ∈ Set.Icc (0 : ℝ) 1

/-- The posterior predictive of the prior `μ` as a rule of the bag `(n, k)` (`CON.PRO.postPred`). -/
noncomputable def proPriorRule (μ : Measure ℝ) (n k : ℕ) : ℝ :=
  PRO.postPred μ (List.replicate k true ++ List.replicate (n - k) false)

theorem integrable_of_bdd01 {μ : Measure ℝ} (hμ : IsPrior01 μ) (f : ℝ → ℝ) (hf : Continuous f)
    (hb : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |f θ| ≤ 1) : Integrable f μ := by
  haveI := hμ.1
  refine Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable ?_
  filter_upwards [hμ.2] with θ hθ
  rw [Real.norm_eq_abs]
  exact hb θ hθ

/-- **Every posterior predictive is a martingale at the node `(1, 1)`.** For a prior on `[0, 1]` whose
relevant moments do not vanish: `f(1,1) = f(1,1) f(2,2) + (1 - f(1,1)) f(2,1)`. -/
theorem postPred_node11 {μ : Measure ℝ} (hμ : IsPrior01 μ) (hA : (∫ θ, θ ∂μ) ≠ 0)
    (hB : (∫ θ, θ * θ ∂μ) ≠ 0) (hD : (∫ θ, θ * (1 - θ) ∂μ) ≠ 0) :
    PRO.postPred μ [true] = PRO.postPred μ [true] * PRO.postPred μ [true, true] +
      (1 - PRO.postPred μ [true]) * PRO.postPred μ [true, false] := by
  have hI1 : Integrable (fun θ : ℝ => θ) μ :=
    integrable_of_bdd01 hμ _ continuous_id (fun θ hθ => abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩)
  have hI2 : Integrable (fun θ : ℝ => θ * θ) μ :=
    integrable_of_bdd01 hμ _ (by fun_prop) (fun θ hθ => abs_le.mpr
      ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩)
  have hI3 : Integrable (fun θ : ℝ => θ * (θ * θ)) μ :=
    integrable_of_bdd01 hμ _ (by fun_prop) (fun θ hθ => abs_le.mpr
      ⟨by nlinarith [hθ.1, hθ.2, mul_nonneg hθ.1 hθ.1, mul_nonneg hθ.1 (mul_nonneg hθ.1 hθ.1)],
       by nlinarith [hθ.1, hθ.2, mul_nonneg hθ.1 hθ.1, mul_le_one₀ hθ.2 hθ.1 hθ.2]⟩)
  have eD : (∫ θ, θ * (1 - θ) ∂μ) = (∫ θ, θ ∂μ) - ∫ θ, θ * θ ∂μ := by
    rw [← integral_sub hI1 hI2]
    congr 1
    funext θ
    ring
  have eE : (∫ θ, θ * (θ * (1 - θ)) ∂μ) = (∫ θ, θ * θ ∂μ) - ∫ θ, θ * (θ * θ) ∂μ := by
    rw [← integral_sub hI2 hI3]
    congr 1
    funext θ
    ring
  have b1 : ∀ θ : ℝ, PRO.bernLik θ [true] = θ := fun θ => by simp [PRO.bernLik]
  have b2 : ∀ θ : ℝ, PRO.bernLik θ [true, true] = θ * θ := fun θ => by simp [PRO.bernLik]
  have b3 : ∀ θ : ℝ, PRO.bernLik θ [true, false] = θ * (1 - θ) := fun θ => by simp [PRO.bernLik]
  simp only [PRO.postPred, b1, b2, b3]
  rw [eD] at hD ⊢
  rw [eE]
  generalize (∫ θ, θ ∂μ) = A at hA hD ⊢
  generalize (∫ θ, θ * θ ∂μ) = B at hB hD ⊢
  generalize (∫ θ, θ * (θ * θ) ∂μ) = C
  field_simp <;> ring

/-- **Every posterior predictive is a martingale at the node `(1, 0)`.**
`f(1,0) = f(1,0) f(2,1) + (1 - f(1,0)) f(2,0)`. -/
theorem postPred_node10 {μ : Measure ℝ} (hμ : IsPrior01 μ) (hA : (∫ θ, (1 - θ) ∂μ) ≠ 0)
    (hF : (∫ θ, (1 - θ) * (1 - θ) ∂μ) ≠ 0) (hD : (∫ θ, θ * (1 - θ) ∂μ) ≠ 0) :
    PRO.postPred μ [false] = PRO.postPred μ [false] * PRO.postPred μ [true, false] +
      (1 - PRO.postPred μ [false]) * PRO.postPred μ [false, false] := by
  have hI1 : Integrable (fun θ : ℝ => 1 - θ) μ :=
    integrable_of_bdd01 hμ _ (by fun_prop) (fun θ hθ => abs_le.mpr ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
  have hI2 : Integrable (fun θ : ℝ => θ * (1 - θ)) μ :=
    integrable_of_bdd01 hμ _ (by fun_prop) (fun θ hθ => abs_le.mpr
      ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩)
  have hI3 : Integrable (fun θ : ℝ => θ * (θ * (1 - θ))) μ :=
    integrable_of_bdd01 hμ _ (by fun_prop) (fun θ hθ => abs_le.mpr
      ⟨by nlinarith [hθ.1, hθ.2, mul_nonneg hθ.1 hθ.1, mul_nonneg (mul_nonneg hθ.1 hθ.1) (sub_nonneg.mpr hθ.2)],
       by nlinarith [hθ.1, hθ.2, mul_nonneg hθ.1 hθ.1, mul_nonneg (mul_nonneg hθ.1 hθ.1) (sub_nonneg.mpr hθ.2),
         mul_le_one₀ hθ.2 hθ.1 hθ.2]⟩)
  have eF : (∫ θ, (1 - θ) * (1 - θ) ∂μ) = (∫ θ, (1 - θ) ∂μ) - ∫ θ, θ * (1 - θ) ∂μ := by
    rw [← integral_sub hI1 hI2]
    congr 1
    funext θ
    ring
  have eG : (∫ θ, θ * ((1 - θ) * (1 - θ)) ∂μ) = (∫ θ, θ * (1 - θ) ∂μ) - ∫ θ, θ * (θ * (1 - θ)) ∂μ := by
    rw [← integral_sub hI2 hI3]
    congr 1
    funext θ
    ring
  have b1 : ∀ θ : ℝ, PRO.bernLik θ [false] = 1 - θ := fun θ => by simp [PRO.bernLik]
  have b2 : ∀ θ : ℝ, PRO.bernLik θ [false, false] = (1 - θ) * (1 - θ) := fun θ => by simp [PRO.bernLik]
  have b3 : ∀ θ : ℝ, PRO.bernLik θ [true, false] = θ * (1 - θ) := fun θ => by simp [PRO.bernLik]
  simp only [PRO.postPred, b1, b2, b3]
  rw [eF] at hF ⊢
  rw [eG]
  generalize (∫ θ, (1 - θ) ∂μ) = A at hA hF ⊢
  generalize (∫ θ, θ * (1 - θ) ∂μ) = D at hD hF ⊢
  generalize (∫ θ, θ * (θ * (1 - θ)) ∂μ) = E
  field_simp <;> ring

/-- **The table against Laplace's rule.** Any predictor whose order averages match `CON.PRO.tbl` on the
bags with `n ≤ 1` is not within `ε` of Laplace's rule for any `ε < 0.1426` (bag `(1, 1)`: `0.5239`
against `2/3`). The tiny result's tolerance is `0.0034`. -/
theorem pro_table_refutes_laplace (q : List Bool → ℝ) (h : PRO.TableHolds q 1) (ε : ℝ)
    (hε : ε < 1426 / 10000) : ¬ PRO.BayesInExpectation q PRO.laplace 1 ε := by
  intro hb
  have h1 := abs_le.mp (h 1 1 le_rfl le_rfl)
  have h2 := abs_le.mp (hb 1 1 le_rfl le_rfl)
  have e1 : ((PRO.bagTable 1 1 : ℤ) : ℝ) = 5239 := by
    have : PRO.bagTable 1 1 = 5239 := by decide
    rw [this]
    norm_num
  have e2 : PRO.laplace 1 1 = 2 / 3 := by
    unfold PRO.laplace
    norm_num
  rw [e1] at h1
  rw [e2] at h2
  linarith [h1.2, h2.1]

/-- **The table against every prior.** Any predictor whose order averages match `CON.PRO.tbl` on the
bags with `n ≤ 2` is not within `0.044` of the posterior predictive of any prior on `[0, 1]`: the bags
`(1,1)`, `(2,1)`, `(2,2)` (`0.5239`, `0.4940`, `0.7056`) violate the martingale identity that every
posterior predictive satisfies. -/
theorem pro_table_no_prior (q : List Bool → ℝ) (h : PRO.TableHolds q 2) (μ : Measure ℝ)
    (hμ : IsPrior01 μ) : ¬ PRO.BayesInExpectation q (proPriorRule μ) 2 (44 / 1000) := by
  intro hb
  have t11 := abs_le.mp (h 1 1 (by norm_num) le_rfl)
  have t21 := abs_le.mp (h 2 1 le_rfl (by norm_num))
  have t22 := abs_le.mp (h 2 2 le_rfl le_rfl)
  have c11 := abs_le.mp (hb 1 1 (by norm_num) le_rfl)
  have c21 := abs_le.mp (hb 2 1 le_rfl (by norm_num))
  have c22 := abs_le.mp (hb 2 2 le_rfl le_rfl)
  have e11 : ((PRO.bagTable 1 1 : ℤ) : ℝ) = 5239 := by
    have : PRO.bagTable 1 1 = 5239 := by decide
    rw [this]; norm_num
  have e21 : ((PRO.bagTable 2 1 : ℤ) : ℝ) = 4940 := by
    have : PRO.bagTable 2 1 = 4940 := by decide
    rw [this]; norm_num
  have e22 : ((PRO.bagTable 2 2 : ℤ) : ℝ) = 7056 := by
    have : PRO.bagTable 2 2 = 7056 := by decide
    rw [this]; norm_num
  have r11 : proPriorRule μ 1 1 = PRO.postPred μ [true] := rfl
  have r21 : proPriorRule μ 2 1 = PRO.postPred μ [true, false] := rfl
  have r22 : proPriorRule μ 2 2 = PRO.postPred μ [true, true] := rfl
  rw [e11] at t11
  rw [e21] at t21
  rw [e22] at t22
  rw [r11] at c11
  rw [r21] at c21
  rw [r22] at c22
  -- bounds on the three predictive values
  have f11lo : (4798 : ℝ) / 10000 ≤ PRO.postPred μ [true] := by linarith [t11.1, c11.2]
  have f11hi : PRO.postPred μ [true] ≤ (5680 : ℝ) / 10000 := by linarith [t11.2, c11.1]
  have f21lo : (4499 : ℝ) / 10000 ≤ PRO.postPred μ [true, false] := by linarith [t21.1, c21.2]
  have f22lo : (6615 : ℝ) / 10000 ≤ PRO.postPred μ [true, true] := by linarith [t22.1, c22.2]
  have b1 : ∀ θ : ℝ, PRO.bernLik θ [true] = θ := fun θ => by simp [PRO.bernLik]
  have b2 : ∀ θ : ℝ, PRO.bernLik θ [true, true] = θ * θ := fun θ => by simp [PRO.bernLik]
  have b3 : ∀ θ : ℝ, PRO.bernLik θ [true, false] = θ * (1 - θ) := fun θ => by simp [PRO.bernLik]
  by_cases hA : (∫ θ, θ ∂μ) = 0
  · have z : PRO.postPred μ [true] = 0 := by
      simp only [PRO.postPred, b1, hA, div_zero]
    rw [z] at f11lo
    norm_num at f11lo
  by_cases hB : (∫ θ, θ * θ ∂μ) = 0
  · have z : PRO.postPred μ [true, true] = 0 := by
      simp only [PRO.postPred, b2, hB, div_zero]
    rw [z] at f22lo
    norm_num at f22lo
  by_cases hD : (∫ θ, θ * (1 - θ) ∂μ) = 0
  · have z : PRO.postPred μ [true, false] = 0 := by
      simp only [PRO.postPred, b3, hD, div_zero]
    rw [z] at f21lo
    norm_num at f21lo
  have key := postPred_node11 hμ hA hB hD
  have p1 : 0 ≤ PRO.postPred μ [true] * (PRO.postPred μ [true, true] - 6615 / 10000) :=
    mul_nonneg (by linarith) (by linarith)
  have p2 : 0 ≤ (1 - PRO.postPred μ [true]) * (PRO.postPred μ [true, false] - 4499 / 10000) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [key, p1, p2]

/-- `TableHolds` and `BayesInExpectation` restrict to smaller bags. -/
theorem tableHolds_mono {q : List Bool → ℝ} {N M : ℕ} (hNM : M ≤ N) (h : PRO.TableHolds q N) :
    PRO.TableHolds q M := fun n k hn hk => h n k (hn.trans hNM) hk

theorem bie_mono {q : List Bool → ℝ} {ref : ℕ → ℕ → ℝ} {N M : ℕ} {ε : ℝ} (hNM : M ≤ N)
    (h : PRO.BayesInExpectation q ref N ε) : PRO.BayesInExpectation q ref M ε :=
  fun n k hn hk => h n k (hn.trans hNM) hk

/-- **`Cert8` excludes the tiny tolerance.** If `Cert8` holds, the red/blue predictor
`p` is not within `ε` of Laplace's rule on the 45 bags for any `ε < 0.1426`; the tiny result has `0.0034`. -/
theorem pro_cert_refutes_laplace (h : PRO.Cert8) (ε : ℝ) (hε : ε < 1426 / 10000) :
    ¬ PRO.BayesInExpectation PRO.p PRO.laplace 8 ε := fun hb =>
  pro_table_refutes_laplace PRO.p (tableHolds_mono (by norm_num) (PRO.numerics_of_checks h).1) ε hε
    (bie_mono (by norm_num) hb)

/-- **`Cert8` excludes every prior.** If `Cert8` holds, `p` is not within `0.044` of the posterior
predictive of any prior on `[0, 1]`, already on the bags with `n ≤ 2`. -/
theorem pro_cert_no_prior (h : PRO.Cert8) (μ : Measure ℝ) (hμ : IsPrior01 μ) :
    ¬ PRO.BayesInExpectation PRO.p (proPriorRule μ) 8 (44 / 1000) := fun hb =>
  pro_table_no_prior PRO.p (tableHolds_mono (by norm_num) (PRO.numerics_of_checks h).1) μ hμ
    (bie_mono (by norm_num) hb)

/-- The same from the hypothesis of `PRO.main_small` (7 prompts). -/
theorem pro_small_cert_no_prior (h : PRO.BagCerts 2) (μ : Measure ℝ) (hμ : IsPrior01 μ) :
    ¬ PRO.BayesInExpectation PRO.p (proPriorRule μ) 2 (44 / 1000) :=
  pro_table_no_prior PRO.p (PRO.table_of_certs h) μ hμ

theorem pro_small_cert_refutes_laplace (h : PRO.BagCerts 2) (ε : ℝ) (hε : ε < 1426 / 10000) :
    ¬ PRO.BayesInExpectation PRO.p PRO.laplace 2 ε := fun hb =>
  pro_table_refutes_laplace PRO.p (tableHolds_mono (by norm_num) (PRO.table_of_certs h)) ε hε
    (bie_mono (by norm_num) hb)

/-! ## The tolerances of `TinyTheorem` do not force Bayesian behaviour

At the tiny result's `ε = 0.0034` the criterion forces the order average to rise by at least `0.09` with
every additional one. At the tolerances of `TinyTheorem` (`0.143` to Laplace, `0.073` to Beta(2, 9/4)) it does not even
force it to rise: `antiPred` meets the whole `TinyTheorem`, and its order average falls when a zero is
replaced by a one. No posterior predictive of any prior does that. -/

/-- At the tiny tolerance the order average increases by more than `0.09` with every additional one. -/
theorem tiny_tolerance_forces_increase (q : List Bool → ℝ)
    (h : PRO.BayesInExpectation q PRO.laplace 8 (34 / 10000)) (n k : ℕ) (hn : n ≤ 8) (hk : k < n) :
    PRO.avg q n k + 9 / 100 < PRO.avg q n (k + 1) := by
  have h0 := abs_le.mp (h n k hn hk.le)
  have h1 := abs_le.mp (h n (k + 1) hn hk)
  have hn' : (n : ℝ) ≤ 8 := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have e : PRO.laplace n (k + 1) - PRO.laplace n k = 1 / ((n : ℝ) + 2) := by
    unfold PRO.laplace
    push_cast
    rw [← sub_div]
    congr 1
    ring
  have hge : (1 : ℝ) / 10 ≤ 1 / ((n : ℝ) + 2) := one_div_le_one_div_of_le hpos (by linarith)
  linarith [h0.2, h1.1]

/-- An order effect on the two orderings of the bag `(2, 1)` only. -/
noncomputable def antiOrd (x : List Bool) : ℝ :=
  if x = [true, false] then 26 / 100 else if x = [false, true] then -(26 / 100) else 0

/-- The Beta(2, 9/4) rule, raised by `0.07` on the bag `(8, 4)` and lowered by `0.07` on `(8, 5)`. -/
noncomputable def antiRule (n k : ℕ) : ℝ :=
  PRO.betaRule 2 (9 / 4) n k +
    (if n = 8 ∧ k = 4 then 7 / 100 else if n = 8 ∧ k = 5 then -(7 / 100) else 0)

/-- A predictor that meets `TinyTheorem` and is not monotone in the evidence. -/
noncomputable def antiPred (x : List Bool) : ℝ := antiRule x.length (x.count true) + antiOrd x

theorem avg_add_bag (f : ℕ → ℕ → ℝ) (d : List Bool → ℝ) {n k : ℕ} (hk : k ≤ n) :
    PRO.avg (fun x => f x.length (x.count true) + d x) n k = f n k + PRO.avg d n k := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k),
      f (List.ofFn x).length ((List.ofFn x).count true) + d (List.ofFn x) = f n k + d (List.ofFn x) := by
    intro x hx
    have hc := (Finset.mem_filter.mp hx).2
    rw [List.length_ofFn, hc]
  have hs := Finset.sum_congr rfl h
  have hconst : (1 / (n.choose k : ℝ)) *
      ∑ _x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k), f n k = f n k :=
    PRO.avg_const (f n k) hk
  show (1 / (n.choose k : ℝ)) *
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k),
        (f (List.ofFn x).length ((List.ofFn x).count true) + d (List.ofFn x)) =
    f n k + (1 / (n.choose k : ℝ)) *
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k), d (List.ofFn x)
  rw [hs, Finset.sum_add_distrib, mul_add, hconst]

theorem avg_antiOrd (n k : ℕ) : PRO.avg antiOrd n k = 0 := by
  by_cases h21 : n = 2 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := h21
    unfold PRO.avg
    rw [PRO.bag_sum antiOrd 2 1]
    have e : PRO.orderings 2 1 = [[false, true], [true, false]] := by decide
    rw [e]
    norm_num [antiOrd]
  · have h : ∀ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k),
        antiOrd (List.ofFn x) = 0 := by
      intro x hx
      have hc := (Finset.mem_filter.mp hx).2
      have hl : (List.ofFn x).length = n := List.length_ofFn
      have h1 : List.ofFn x ≠ [true, false] := by
        intro he
        rw [he] at hl hc
        exact h21 ⟨by simpa using hl.symm, by simpa using hc.symm⟩
      have h2 : List.ofFn x ≠ [false, true] := by
        intro he
        rw [he] at hl hc
        exact h21 ⟨by simpa using hl.symm, by simpa using hc.symm⟩
      simp [antiOrd, h1, h2]
    unfold PRO.avg
    rw [Finset.sum_congr rfl h]
    simp

theorem avg_antiPred (n k : ℕ) (hk : k ≤ n) : PRO.avg antiPred n k = antiRule n k := by
  have h := avg_add_bag antiRule antiOrd hk
  rw [avg_antiOrd, add_zero] at h
  exact h

theorem antiRule_laplace (n k : ℕ) (hn : n ≤ 8) (hk : k ≤ n) :
    |antiRule n k - PRO.laplace n k| ≤ 143 / 1000 := by
  interval_cases n <;> interval_cases k <;>
    norm_num [antiRule, PRO.laplace, PRO.betaRule, abs_le]

theorem antiRule_beta (n k : ℕ) : |antiRule n k - PRO.betaRule 2 (9 / 4) n k| ≤ 73 / 1000 := by
  unfold antiRule
  rw [add_sub_cancel_left]
  split_ifs <;> norm_num [abs_le]

/-- **`TinyTheorem` admits an anti-monotone predictor.** `antiPred` satisfies `TinyTheorem` with
its constants, and its order average on the bag `(8, 5)` is lower than on `(8, 4)` by more than
`0.05`: one more ` red` among eight observations lowers its averaged probability of ` red`. -/
theorem pro_tolerances_admit_antimonotone :
    PRO.TinyTheorem antiPred 8 (143 / 1000) (73 / 1000) (52 / 100) ∧
      PRO.avg antiPred 8 5 + 5 / 100 < PRO.avg antiPred 8 4 := by
  have hgap : (52 / 100 : ℝ) ≤ |antiPred [true, false] - antiPred [false, true]| := by
    have e1 : antiPred [true, false] = antiRule 2 1 + 26 / 100 := by
      norm_num [antiPred, antiOrd]
    have e2 : antiPred [false, true] = antiRule 2 1 - 26 / 100 := by
      norm_num [antiPred, antiOrd] <;> ring
    have e : antiPred [true, false] - antiPred [false, true] = 52 / 100 := by
      rw [e1, e2]
      ring
    rw [e]
    norm_num
  refine ⟨⟨?_, ?_, PRO.corollaries_of_gap (x := [true, false]) (x' := [false, true])
    (List.perm_iff_count.mpr fun a => by cases a <;> rfl) (by norm_num) hgap⟩, ?_⟩
  · intro n k hn hk
    rw [avg_antiPred n k hk]
    exact antiRule_laplace n k hn hk
  · intro n k hn hk
    rw [avg_antiPred n k hk]
    exact antiRule_beta n k
  · rw [avg_antiPred 8 5 (by norm_num), avg_antiPred 8 4 (by norm_num)]
    norm_num [antiRule, PRO.betaRule]


end CON
