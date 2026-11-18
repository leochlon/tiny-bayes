import Mathlib
import CON.PRO.Claim
import CON.PRO.Sound

/-! # Main result

* `main`: the tiny-transformer theorem holds for Pythia-14M on the same 45 bags (`n ≤ 8`), provided
  the integer computations `Cert8` evaluate to `true`. `Cert8` contains no real numbers: it runs the
  interval forward pass of `PRO.Mirror` on the 511 prompts and compares integers with a table.
* `enclosure`: that interval forward pass encloses the real model `p` on every prompt.
* `tiny_of_numerics`, `numerics_of_checks`: the two halves of `main`, through the numerical facts
  `Numerics8` about `p`.
* `const_not_bayes`: the criterion is not vacuous; no constant predictor meets it. -/

namespace CON.PRO

/-- The numerical facts about Pythia-14M that the claim rests on: the 45 order averages of `p` to
`10^-4` (`tbl`), and one pair of orderings of the bag `(8, 4)`, ` blue` four times then ` red` four
times against the reverse order, at least `0.52` apart. -/
def Numerics8 : Prop :=
  TableHolds p 8 ∧
  (52 / 100 : ℝ) ≤ p [false, false, false, false, true, true, true, true] -
    p [true, true, true, true, false, false, false, false]

/-- The tiny-transformer theorem for Pythia-14M on the 45 bags with `n ≤ 8`, from `Numerics8`. -/
theorem tiny_of_numerics (h : Numerics8) : TinyTheorem p 8 (143 / 1000) (73 / 1000) (52 / 100) := by
  obtain ⟨ht, hg⟩ := h
  exact tiny_of_table (le_refl 8) ht
    (x := [false, false, false, false, true, true, true, true])
    (x' := [true, true, true, true, false, false, false, false])
    (List.perm_iff_count.mpr fun a => by cases a <;> rfl) (by norm_num) (hg.trans (le_abs_self _))

/-- **Soundness of the interval forward pass**: for every binary sequence, Pythia-14M's
renormalised probability `p x` lies in the computed interval `pI x`. -/
theorem enclosure (x : List Bool) : memAt S (p x) (pI x) := p_sound x

/-- The bag checks for `n ≤ N`: the interval enclosure of each order average lies within `10^-4` of
the table entry. A closed, decidable statement about integers. -/
def BagCerts (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → ∀ k : ℕ, k ≤ n →
    bagCheck n k ((bagTable n k - 1) * 1000000) ((bagTable n k + 1) * 1000000) = true

/-- The integer computations that certify `Numerics8`: the 45 bag checks and one gap check. -/
def Cert8 : Prop :=
  BagCerts 8 ∧
  gapCheck [false, false, false, false, true, true, true, true]
    [true, true, true, true, false, false, false, false] 5200000000 10000000000 = true

/-- `BagCerts N` and `Cert8` are decidable: finitely many integer comparisons. -/
instance (N : ℕ) : Decidable (BagCerts N) := by
  unfold BagCerts
  infer_instance

instance : Decidable Cert8 := by
  unfold Cert8
  infer_instance

theorem table_of_certs {N : ℕ} (h : BagCerts N) : TableHolds p N := by
  intro n k hn hk
  obtain ⟨h1, h2⟩ := bag_encl hk (h n hn k hk)
  have e1 : (((bagTable n k - 1) * 1000000 : ℤ) : ℝ) / 10 ^ 10 = ((bagTable n k : ℝ) - 1) / 10000 := by
    push_cast
    ring
  have e2 : (((bagTable n k + 1) * 1000000 : ℤ) : ℝ) / 10 ^ 10 = ((bagTable n k : ℝ) + 1) / 10000 := by
    push_cast
    ring
  rw [e1] at h1
  rw [e2] at h2
  unfold avg
  rw [abs_le]
  constructor <;> linarith

/-- If the interval computations succeed, the numerical facts hold. -/
theorem numerics_of_checks (h : Cert8) : Numerics8 := by
  obtain ⟨hb, hg⟩ := h
  have hgap := (gap_encl hg).1
  have e : ((5200000000 : ℤ) : ℝ) / 10 ^ 10 = 52 / 100 := by norm_num
  rw [e] at hgap
  exact ⟨table_of_certs hb, hgap⟩

/-- **The tiny-transformer theorem for Pythia-14M on the same 45 bags.** If the interval
computations `Cert8` evaluate to `true`, then: on every bag with `n ≤ 8` the order average of `p` is
within `0.143` of Laplace's rule and within `0.073` of the `Beta(2, 9/4)` posterior predictive; two
orderings of one bag differ by at least `0.52`; `p` is no function of the bag, equals no
exchangeable predictor and no posterior predictive, and is at least `0.26` from every posterior
predictive at some prompt. -/
theorem main (h : Cert8) : TinyTheorem p 8 (143 / 1000) (73 / 1000) (52 / 100) :=
  tiny_of_numerics (numerics_of_checks h)

/-- The same on the 6 bags with `n ≤ 2` and the two orderings of the bag `(2, 1)`: 7 prompts. -/
theorem main_small (hb : BagCerts 2)
    (hg : gapCheck [false, true] [true, false] 2800000000 10000000000 = true) :
    TinyTheorem p 2 (143 / 1000) (73 / 1000) (28 / 100) := by
  have hgap := (gap_encl hg).1
  have e : ((2800000000 : ℤ) : ℝ) / 10 ^ 10 = 28 / 100 := by norm_num
  rw [e] at hgap
  exact tiny_of_table (by norm_num) (table_of_certs hb) (x := [false, true]) (x' := [true, false])
    (List.perm_iff_count.mpr fun a => by cases a <;> rfl) (by norm_num) (hgap.trans (le_abs_self _))

/-- The order average of a constant predictor is that constant. -/
theorem avg_const (c : ℝ) {n k : ℕ} (hk : k ≤ n) : avg (fun _ => c) n k = c := by
  unfold avg
  rw [bag_sum (fun _ => c) n k]
  have hC : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, orderings_length]
  field_simp

/-- The criterion is not vacuous: no predictor that ignores the prompt is within `0.143` of
Laplace's rule on the bags with `n ≤ 8`. -/
theorem const_not_bayes (c : ℝ) : ¬ BayesInExpectation (fun _ => c) laplace 8 (143 / 1000) := by
  intro h
  have h0 := h 8 0 (le_refl 8) (by norm_num)
  have h8 := h 8 8 (le_refl 8) (le_refl 8)
  rw [avg_const c (by norm_num)] at h0 h8
  unfold laplace at h0 h8
  rw [abs_le] at h0 h8
  obtain ⟨-, a2⟩ := h0
  obtain ⟨b1, -⟩ := h8
  norm_num at a2 b1
  linarith

end CON.PRO
