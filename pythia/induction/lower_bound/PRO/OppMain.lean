import Mathlib
import PRO.Pythia
import PRO.OppData
import PRO.OppInduction

/-! The module `CON.Main` of the first version of `upper_bound/`, under the namespace `PRO.Opp`. -/

/-! # The induction claim about pythia-14m, and its refutation by pigeonhole

`pythia14m` (`CON.Pythia`) is the exact model over the reals. `logitAt`, `repSeq`, `InductionOn`,
`FailsOn`, `Fail3` are defined in `CON.Induction`; `V` and `groups` are the literal lists of `CON.Data`. -/

namespace PRO

namespace Opp

noncomputable section

/-- The claim: there are a set `V'` of at least 1,000 tokens of `V` and a margin `δ > 0`
such that pythia-14m performs induction with margin `δ` on every repeated sequence over `V'`
(`InductionOn`: all lists `r` of distinct tokens of `V'` with `3 ≤ m ≤ 8`, all `2 ≤ k ≤ m - 1`, the
logit of `r_{k+1}` at the second `r_k` beats every other token `t < 50304` by at least `δ`). -/
def Claim : Prop :=
  ∃ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) ∧ 1000 ≤ V'.card ∧
    ∃ δ : ℝ, 0 < δ ∧ InductionOn pythia14m V' δ

/-- The group number of a token: the index of the first list of `groups` containing it. -/
def cls (t : ℕ) : ℕ := groups.findIdx (fun g => g.contains t) % numGroups

/-- The certificate. For every group `c` and every set `S` of tokens of `V` in group `c` with more
than `caps[c]` elements, pythia-14m fails on some repeated sequence of distinct tokens of `S`
(`FailsOn`: some `r`, `k` as in the claim and some other token whose logit is at least that of
`r_{k+1}`). A finite statement about logits of the exact model, implied by finitely many explicit
inequalities; it is not proved here (checked in float64 only). -/
def GroupCert : Prop :=
  ∀ (c : ℕ) (S : Finset ℕ), (∀ x ∈ S, x ∈ V) → (∀ x ∈ S, cls x = c) → caps.getD c 0 < S.card →
    FailsOn pythia14m S

theorem cls_lt (a : ℕ) : cls a < numGroups := Nat.mod_lt _ (by decide)

/-- The capacities add up to 831, less than 1,000 (kernel computation). -/
theorem caps_total : ∑ c ∈ Finset.range numGroups, caps.getD c 0 = 831 := by decide +kernel

theorem caps_sum : ∑ c ∈ Finset.range numGroups, caps.getD c 0 < 1000 := by
  rw [caps_total]; norm_num

/-- Shape of the data (kernel computation): `V` has 5,000 entries; `groups` has `numGroups = 167`
lists with 5,000 entries in all, and one capacity per group. -/
theorem data_shape : V.length = 5000 ∧ groups.length = numGroups ∧ numGroups = 167 ∧
    (groups.map List.length).sum = 5000 ∧ caps.length = numGroups := by decide +kernel

/-- One failing sequence over `S` refutes the claim's property for every `V' ⊇ S` and every `δ > 0`. -/
theorem failing_sequence_excludes {S V' : Finset ℕ} {δ : ℝ} (hf : FailsOn pythia14m S)
    (hS : S ⊆ V') (hδ : 0 < δ) : ¬ InductionOn pythia14m V' δ :=
  failsOn_excludes' pythia14m hf hS hδ

/-- The case `m = 3`: one failing triple refutes every `V'` containing its three tokens. -/
theorem failing_triple_excludes {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) {x y z : ℕ}
    (hx : x ∈ V') (hy : y ∈ V') (hz : z ∈ V') (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf : Fail3 pythia14m x y z) : ¬ InductionOn pythia14m V' δ :=
  fail3_excludes' pythia14m hδ hx hy hz hxy hxz hyz hf

/-- For every parameter assignment `θ` of this architecture: two tokens with the same input embedding
cannot both lie in `V'` (given two further tokens of `V'`). -/
theorem twins_excluded (θ : Params) {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) {x y a b : ℕ}
    (hx : x ∈ V') (hy : y ∈ V') (ha : a ∈ V') (hb : b ∈ V')
    (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (hav : a < 50304) (hbv : b < 50304) (he : θ.emb a = θ.emb b) : ¬ InductionOn θ V' δ :=
  twin_excludes' θ hδ hx hy ha hb hxy hxa hxb hya hyb hab hav hbv he

/-- Pigeonhole, for every parameter assignment: with `N` classes and a failure among every `j + 1`
tokens of a class, no `V'` with more than `N * j` tokens works. -/
theorem classes_exclude (θ : Params) (f : ℕ → ℕ) (N j : ℕ) (hf : ∀ a, f a < N)
    {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (hcard : N * j < V'.card)
    (hfail : ∀ S : Finset ℕ, S ⊆ V' → S.card = j + 1 → (∀ x ∈ S, ∀ y ∈ S, f x = f y) →
      FailsOn θ S) : ¬ InductionOn θ V' δ :=
  classes_exclude' θ f N j hf hδ hcard hfail

/-- The margin plays no role: the claim holds exactly when some `V'` of at least 1,000 tokens of `V`
has no failing repeated sequence. So a refutation must exhibit, for every such `V'`, a sequence over
`V'` on which another token's logit reaches that of `r_{k+1}`. -/
theorem claim_iff : Claim ↔
    ∃ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) ∧ 1000 ≤ V'.card ∧ ¬ FailsOn pythia14m V' := by
  constructor
  · rintro ⟨V', hV, hc, hex⟩
    exact ⟨V', hV, hc, (exists_margin_iff' pythia14m V').mp hex⟩
  · rintro ⟨V', hV, hc, hn⟩
    exact ⟨V', hV, hc, (exists_margin_iff' pythia14m V').mpr hn⟩

/-- What a refutation is: every `V'` of at least 1,000 tokens of `V` has a failing sequence. -/
theorem not_claim_iff : ¬ Claim ↔
    ∀ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) → 1000 ≤ V'.card → FailsOn pythia14m V' := by
  rw [claim_iff]
  constructor
  · intro h V' hV hc
    by_contra hn
    exact h ⟨V', hV, hc, hn⟩
  · rintro h ⟨V', hV, hc, hn⟩
    exact hn (h V' hV hc)

/-- Pigeonhole with capacities, for every parameter assignment. -/
theorem capacities_exclude (θ : Params) (f : ℕ → ℕ) (N : ℕ) (cap : ℕ → ℕ) (hf : ∀ a, f a < N)
    {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (hcard : ∑ c ∈ Finset.range N, cap c < V'.card)
    (hfail : ∀ (c : ℕ) (S : Finset ℕ), S ⊆ V' → (∀ x ∈ S, f x = c) → cap c < S.card →
      FailsOn θ S) : ¬ InductionOn θ V' δ :=
  capacities_exclude' θ f N cap hf hδ hcard hfail

/-- Main result. If the certificate holds, the claim is false: a `V'` of at least 1,000 tokens of `V`
has more than `caps[c]` tokens in some group `c` (the capacities add up to less than 1,000), hence a
failing sequence, for every margin `δ > 0`. -/
theorem main (hc : GroupCert) : ¬ Claim := by
  rintro ⟨V', hV, hcard, δ, hδ, hind⟩
  refine capacities_exclude' pythia14m cls numGroups (fun c => caps.getD c 0) cls_lt hδ
    (lt_of_lt_of_le caps_sum hcard) ?_ hind
  intro c S hS hcls hlt
  exact hc c S (fun x hx => hV x (hS hx)) hcls hlt

/-- The same with the count made explicit: under the certificate, induction fails on every set of
more than 831 tokens of `V`, for every positive margin. -/
theorem main_bound (hc : GroupCert) {V' : Finset ℕ} (hV : ∀ x ∈ V', x ∈ V) (hcard : 831 < V'.card)
    {δ : ℝ} (hδ : 0 < δ) : ¬ InductionOn pythia14m V' δ := by
  refine capacities_exclude' pythia14m cls numGroups (fun c => caps.getD c 0) cls_lt hδ
    (by rw [caps_total]; exact hcard) ?_
  intro c S hS hcls hlt
  exact hc c S (fun x hx => hV x (hS hx)) hcls hlt

end

end Opp

end PRO
