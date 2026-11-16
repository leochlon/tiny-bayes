import Mathlib
import CON.Pythia
import CON.Data
import CON.Induction
import CON.Groups
import CON.Search
import CON.Cover
import CON.Count
import CON.PRO.Main

/-! # Induction on repeated sequences in pythia-14m: an upper bound

`pythia14m` (`CON.Pythia`) is the exact model over the reals. `logitAt`, `repSeq`, `InductionOn`,
`FailsOn`, `Fail3`, `FailSome` are defined in `CON.Induction`; `V`, `groups`, `caps`, `freeMasks`,
`caps3`, `slotTab` are the literal data of `CON.Data`; `cls`, `tbit`, `mx` are in `CON.Groups`, `CON.Clique`.
`CON.PRO.*` is the first version of `lower_bound/` (`Main.lean`, `V.lean`) under the namespace
`CON.PRO`, over the same model files. -/

namespace CON

noncomputable section

/-- The claim: there are a set `V'` of at least 1,000 tokens of `V` and a margin `δ > 0`
such that pythia-14m performs induction with margin `δ` on every repeated sequence over `V'`
(`InductionOn`: all lists `r` of distinct tokens of `V'` with `3 ≤ m ≤ 8`, all `2 ≤ k ≤ m - 1`, the
logit of `r_{k+1}` at the second `r_k` beats every other token `t < 50304` by at least `δ`). -/
def Claim : Prop :=
  ∃ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) ∧ 1000 ≤ V'.card ∧
    ∃ δ : ℝ, 0 < δ ∧ InductionOn pythia14m V' δ

/-- The explicit certificate: 638,716 statements, one for each group `c` and each triple of positions
`i < j < l` of the group whose bit in `freeMasks[c]` is clear. Each says that pythia-14m fails on some
order of the three tokens at these positions (`FailSome`: for some order `x, y, z` there is a token
`t ≠ z` whose logit at position 5 of `[0, x, y, z, x, y, z]` is at least that of `z`).
It is not proved here (checked in float64 only). -/
def TripleCert : Prop :=
  ∀ c i j l : ℕ, c < numGroups → i < j → j < l → l < (groups.getD c []).length →
    tbit (freeMasks.getD c 0) i j l = false →
    FailSome pythia14m ((groups.getD c []).getD i 0) ((groups.getD c []).getD j 0)
      ((groups.getD c []).getD l 0)

/-- The second certificate (sequences of up to five tokens, smaller capacities). For every group `c`
and every set `S` of tokens of `V` in group `c` with more than `caps[c]` elements, pythia-14m fails
on some repeated sequence of distinct tokens of `S`. A finite statement about logits of the exact
model, implied by finitely many explicit inequalities; not proved here (checked in float64 only). -/
def GroupCert : Prop :=
  ∀ (c : ℕ) (S : Finset ℕ), (∀ x ∈ S, x ∈ V) → (∀ x ∈ S, cls x = c) → caps.getD c 0 < S.card →
    FailsOn pythia14m S

/-- `TripleCert` has 638,716 instances: the number of triples of positions `i < j < l` of a group
whose bit in the group's mask is clear (kernel computation, `CON.Count`). -/
theorem tripleCert_instances :
    ((List.range numGroups).map fun c =>
      clearCount (freeMasks.getD c 0) (groups.getD c []).length).sum = 638716 := clear_total

/-- The triple capacities add up to 941 (kernel computation). -/
theorem caps3_total : ∑ c ∈ Finset.range numGroups, caps3.getD c 0 = 941 := by decide +kernel

/-- The capacities of the second certificate add up to 831 (kernel computation). -/
theorem caps_total : ∑ c ∈ Finset.range numGroups, caps.getD c 0 = 831 := by decide +kernel

/-- Shape of the data (kernel computation): `V` has 5,000 entries; `groups` has `numGroups = 167`
lists with 5,000 entries in all, and one capacity and one mask per group. -/
theorem data_shape : V.length = 5000 ∧ groups.length = numGroups ∧ numGroups = 167 ∧
    (groups.map List.length).sum = 5000 ∧ caps.length = numGroups ∧ caps3.length = numGroups ∧
    freeMasks.length = numGroups := by decide +kernel

/-! ## What a refutation is -/

/-- The margin plays no role: the claim holds exactly when some `V'` of at least 1,000 tokens of `V`
has no failing repeated sequence. -/
theorem claim_iff : Claim ↔
    ∃ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) ∧ 1000 ≤ V'.card ∧ ¬ FailsOn pythia14m V' := by
  constructor
  · rintro ⟨V', hV, hc, hex⟩
    exact ⟨V', hV, hc, (exists_margin_iff' pythia14m V').mp hex⟩
  · rintro ⟨V', hV, hc, hn⟩
    exact ⟨V', hV, hc, (exists_margin_iff' pythia14m V').mpr hn⟩

/-- A refutation is a failing sequence in every `V'` of at least 1,000 tokens of `V`. -/
theorem not_claim_iff : ¬ Claim ↔
    ∀ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) → 1000 ≤ V'.card → FailsOn pythia14m V' := by
  rw [claim_iff]
  constructor
  · intro h V' hV hc
    by_contra hn
    exact h ⟨V', hV, hc, hn⟩
  · rintro h ⟨V', hV, hc, hn⟩
    exact hn (h V' hV hc)

/-- One failing sequence over `S` refutes the claim's property for every `V' ⊇ S` and every `δ > 0`. -/
theorem failing_sequence_excludes {S V' : Finset ℕ} {δ : ℝ} (hf : FailsOn pythia14m S)
    (hS : S ⊆ V') (hδ : 0 < δ) : ¬ InductionOn pythia14m V' δ :=
  failsOn_excludes' pythia14m hf hS hδ

/-- For every parameter assignment `θ` of this architecture: two tokens with the same input embedding
cannot both lie in `V'` (given two further tokens of `V'`). -/
theorem twins_excluded (θ : Params) {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) {x y a b : ℕ}
    (hx : x ∈ V') (hy : y ∈ V') (ha : a ∈ V') (hb : b ∈ V')
    (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (hav : a < 50304) (hbv : b < 50304) (he : θ.emb a = θ.emb b) : ¬ InductionOn θ V' δ :=
  twin_excludes' θ hδ hx hy ha hb hxy hxa hxb hya hyb hab hav hbv he

/-- Pigeonhole with capacities, for every parameter assignment. -/
theorem capacities_exclude (θ : Params) (f : ℕ → ℕ) (N : ℕ) (cap : ℕ → ℕ) (hf : ∀ a, f a < N)
    {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (hcard : ∑ c ∈ Finset.range N, cap c < V'.card)
    (hfail : ∀ (c : ℕ) (S : Finset ℕ), S ⊆ V' → (∀ x ∈ S, f x = c) → cap c < S.card →
      FailsOn θ S) : ¬ InductionOn θ V' δ :=
  capacities_exclude' θ f N cap hf hδ hcard hfail

/-! ## The explicit certificate suffices: the combinatorics are checked by the kernel -/

/-- Kernel computation (modules `CON.S.*`): for every group the exhaustive search over its positions
stays within `caps3[c]`. -/
theorem search_ok (c : ℕ) (hc : c < 167) :
    mx (freeMasks.getD c 0) (groups.getD c []).length [] ≤ caps3.getD c 0 := searchOK c hc

/-- Soundness of the search: if it stays within `cap`, every set of more than `cap` positions below
`n` contains a triple `i < j < l` whose bit in the mask is clear. -/
theorem search_sound {mask n cap : ℕ} (h : mx mask n [] ≤ cap) {U : Finset ℕ}
    (hU : U ⊆ Finset.range n) (hc : cap < U.card) :
    ∃ i ∈ U, ∃ j ∈ U, ∃ l ∈ U, i < j ∧ j < l ∧ tbit mask i j l = false := clique_bound h hU hc

/-- Kernel computation: every token of `V` is the entry of `groups` that `cls`, `posOf` name. -/
theorem cover_ok : ∀ x ∈ V, posOf x < (groups.getD (cls x) []).length ∧
    (groups.getD (cls x) []).getD (posOf x) 0 = x := cover

/-- Under `TripleCert`, every set of more than `caps3[c]` tokens of `V` in group `c` contains three
tokens on some order of which the model fails. Uses the kernel facts `cover` (every token of `V` is
in its group) and `searchOK` (the exhaustive search over the positions of each group stays within
`caps3[c]`) and the soundness of the search (`clique_bound`). -/
theorem tripleCert_triple (hc : TripleCert) (c : ℕ) (S : Finset ℕ) (hSV : ∀ x ∈ S, x ∈ V)
    (hcls : ∀ x ∈ S, cls x = c) (hlt : caps3.getD c 0 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ FailSome pythia14m a b d := by
  obtain ⟨x0, hx0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcN : c < numGroups := by
    rw [← hcls x0 hx0]
    exact cls_lt x0
  have hmem : ∀ x ∈ S, ∃ i, i < (groups.getD c []).length ∧ (groups.getD c []).getD i 0 = x := by
    intro x hx
    have h1 := cover x (hSV x hx)
    rw [hcls x hx] at h1
    exact ⟨posOf x, h1.1, h1.2⟩
  choose! pos hpos using hmem
  have hinj : Set.InjOn pos (S : Set ℕ) := by
    intro a ha b hb e
    have h1 := (hpos a ha).2
    have h2 := (hpos b hb).2
    rw [e] at h1
    exact h1.symm.trans h2
  have hcard : (S.image pos).card = S.card := Finset.card_image_of_injOn hinj
  have hU : S.image pos ⊆ Finset.range (groups.getD c []).length := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hpos x hx).1
  obtain ⟨i, hi, j, hj, l, hl, hij, hjl, hbit⟩ :=
    clique_bound (searchOK c hcN) hU (by rw [hcard]; exact hlt)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hl
  have hf := hc c (pos a) (pos b) (pos d) hcN hij hjl (hpos d hd).1 hbit
  rw [(hpos a ha).2, (hpos b hb).2, (hpos d hd).2] at hf
  have hab : a ≠ b := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  have had : a ≠ d := fun e => by rw [e] at hij; exact lt_irrefl _ (lt_trans hij hjl)
  have hbd : b ≠ d := fun e => by rw [e] at hjl; exact lt_irrefl _ hjl
  exact ⟨a, ha, b, hb, d, hd, hab, had, hbd, hf⟩

/-- Hence a failing sequence over every such set. -/
theorem tripleCert_group (hc : TripleCert) (c : ℕ) (S : Finset ℕ) (hSV : ∀ x ∈ S, x ∈ V)
    (hcls : ∀ x ∈ S, cls x = c) (hlt : caps3.getD c 0 < S.card) : FailsOn pythia14m S := by
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd, hf⟩ := tripleCert_triple hc c S hSV hcls hlt
  exact failSome_failsOn pythia14m ha hb hd hab had hbd hf

/-- Under the explicit certificate, induction fails on every set of more than 941 tokens of `V`, for
every positive margin. -/
theorem main_bound3 (hc : TripleCert) {V' : Finset ℕ} (hV : ∀ x ∈ V', x ∈ V)
    (hcard : 941 < V'.card) {δ : ℝ} (hδ : 0 < δ) : ¬ InductionOn pythia14m V' δ := by
  refine capacities_exclude' pythia14m cls numGroups (fun c => caps3.getD c 0) cls_lt hδ
    (by rw [caps3_total]; exact hcard) ?_
  intro c S hS hcls hlt
  exact tripleCert_group hc c S (fun x hx => hV x (hS hx)) hcls hlt

/-- Main result. If the 638,716 explicit failures of `TripleCert` hold, the claim is false: a `V'`
of at least 1,000 tokens of `V` has more than `caps3[c]` tokens in some group `c` (the capacities
add up to 941), hence a failing triple, for every margin `δ > 0`. -/
theorem main (hc : TripleCert) : ¬ Claim := by
  rintro ⟨V', hV, hcard, δ, hδ, hind⟩
  exact main_bound3 hc hV (by omega) hδ hind

/-- With the second certificate the bound is 831: induction fails on every set of more than 831
tokens of `V`. -/
theorem main_bound (hc : GroupCert) {V' : Finset ℕ} (hV : ∀ x ∈ V', x ∈ V) (hcard : 831 < V'.card)
    {δ : ℝ} (hδ : 0 < δ) : ¬ InductionOn pythia14m V' δ := by
  refine capacities_exclude' pythia14m cls numGroups (fun c => caps.getD c 0) cls_lt hδ
    (by rw [caps_total]; exact hcard) ?_
  intro c S hS hcls hlt
  exact hc c S (fun x hx => hV x (hS hx)) hcls hlt

/-! ## Relation to the formalisation `CON.PRO` -/

/-- `CON.PRO.V` is `V` (kernel computation). -/
theorem pro_V_eq : PRO.V = V := by decide +kernel

/-- The inner statement of `CON.PRO.ClaimAt` is `InductionOn`. -/
theorem pro_inner_iff (V' : Finset ℕ) (δ : ℝ) :
    (∀ r : List ℕ, PRO.Admissible V' r → ∀ k : ℕ, 2 ≤ k → k + 1 ≤ r.length →
      ∀ t : ℕ, t < 50304 → t ≠ r.getD k 0 → δ ≤ PRO.gap r k t) ↔ InductionOn pythia14m V' δ := by
  constructor
  · intro h r hnd hm h3 h8 k hk2 hkm t ht hne
    have h1 := h r ⟨hnd, hm, h3, h8⟩ k hk2 (by omega) t ht hne
    have e : PRO.gap r k t = logitAt pythia14m (repSeq r) (r.length + k) (r.getD k 0)
        - logitAt pythia14m (repSeq r) (r.length + k) t := rfl
    linarith
  · intro h r hr k hk2 hk1 t ht hne
    have h1 := h r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 k hk2 (by omega) t ht hne
    have e : PRO.gap r k t = logitAt pythia14m (repSeq r) (r.length + k) (r.getD k 0)
        - logitAt pythia14m (repSeq r) (r.length + k) t := rfl
    linarith

/-- `CON.PRO.ClaimAt n` in terms of `InductionOn`. -/
theorem pro_claimAt_iff (n : ℕ) : PRO.ClaimAt n ↔
    ∃ V' : Finset ℕ, (∀ x ∈ V', x ∈ V) ∧ n ≤ V'.card ∧
      ∃ δ : ℝ, 0 < δ ∧ InductionOn pythia14m V' δ := by
  constructor
  · rintro ⟨V', δ, hV, hc, hδ, h⟩
    refine ⟨V', fun x hx => ?_, hc, δ, hδ, (pro_inner_iff V' δ).mp h⟩
    rw [← pro_V_eq]
    exact hV x hx
  · rintro ⟨V', hV, hc, δ, hδ, h⟩
    refine ⟨V', δ, fun x hx => ?_, hc, hδ, (pro_inner_iff V' δ).mpr h⟩
    rw [pro_V_eq]
    exact hV x hx

/-- The two formalisations state the same claim: `CON.PRO.Claim ↔ Claim`. -/
theorem pro_claim_iff : PRO.Claim ↔ Claim := pro_claimAt_iff 1000

/-- Under the explicit certificate `CON.PRO.Claim` is false. -/
theorem pro_claim_refuted (hc : TripleCert) : ¬ PRO.Claim :=
  fun h => main hc (pro_claim_iff.mp h)

/-- Under the explicit certificate `CON.PRO.NormalForm` (the other side of `CON.PRO.main`) is false. -/
theorem pro_normalForm_refuted (hc : TripleCert) : ¬ PRO.NormalForm :=
  fun h => pro_claim_refuted hc (PRO.main.mpr h)

/-- Under the explicit certificate `CON.PRO.ClaimAt n` is false for every `n > 941`. -/
theorem pro_claimAt_refuted (hc : TripleCert) (n : ℕ) (hn : 941 < n) : ¬ PRO.ClaimAt n := by
  intro h
  obtain ⟨V', hV, hcard, δ, hδ, hind⟩ := (pro_claimAt_iff n).mp h
  exact main_bound3 hc hV (lt_of_lt_of_le hn hcard) hδ hind

/-- The same for `CON.PRO.NormalFormAt n`. -/
theorem pro_normalFormAt_refuted (hc : TripleCert) (n : ℕ) (hn : 941 < n) : ¬ PRO.NormalFormAt n :=
  fun h => pro_claimAt_refuted hc n hn ((PRO.claimAt_iff_normalFormAt n).mpr h)

/-- Under the second certificate `CON.PRO.ClaimAt n` is false for every `n > 831`. -/
theorem pro_claimAt_refuted_groups (hc : GroupCert) (n : ℕ) (hn : 831 < n) : ¬ PRO.ClaimAt n := by
  intro h
  obtain ⟨V', hV, hcard, δ, hδ, hind⟩ := (pro_claimAt_iff n).mp h
  exact main_bound hc hV (lt_of_lt_of_le hn hcard) hδ hind

/-- With the causality theorem of `CON.PRO`, each failure of the certificate is an inequality between two
next-token logits of one six-token prompt `[BOS, x, y, z, x, y]`. -/
theorem fail3_iff_prompt (θ : Params) (x y z : ℕ) : Fail3 θ x y z ↔
    ∃ t : ℕ, t < 50304 ∧ t ≠ z ∧ logit θ [0, x, y, z, x, y] z ≤ logit θ [0, x, y, z, x, y] t := by
  have e : ∀ t, logitAt θ [0, x, y, z, x, y, z] 5 t = logit θ [0, x, y, z, x, y] t := fun t =>
    PRO.logitAt_eq_logit_take θ [0, x, y, z, x, y, z] 5 t (by simp)
  constructor
  · rintro ⟨t, ht, hne, hle⟩
    exact ⟨t, ht, hne, by rw [← e z, ← e t]; exact hle⟩
  · rintro ⟨t, ht, hne, hle⟩
    exact ⟨t, ht, hne, by rw [e z, e t]; exact hle⟩

/-- On `CON.PRO.claim_triples`: under the explicit certificate its conclusion is false. No
1,000 tokens of `V` pass even the smallest cases (`m = 3`, prompts `[BOS, a, b, c, a, b]`). -/
theorem pro_triples_refuted (hc : TripleCert) :
    ¬ ∃ V' : Finset ℕ, (∀ t ∈ V', t ∈ PRO.V) ∧ V'.card = 1000 ∧
      ∀ a ∈ V', ∀ b ∈ V', ∀ c ∈ V', a ≠ b → a ≠ c → b ≠ c → ∀ t : ℕ, t < 50304 → t ≠ c →
        logit pythia14m [0, a, b, c, a, b] t < logit pythia14m [0, a, b, c, a, b] c := by
  rintro ⟨V', hV, hcard, h⟩
  obtain ⟨c, S, hS, hcls, hlt⟩ := exists_overfull cls numGroups (fun c => caps3.getD c 0) cls_lt
    (V' := V') (by rw [caps3_total, hcard]; norm_num)
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd, hf⟩ := tripleCert_triple hc c S
    (fun x hx => by rw [← pro_V_eq]; exact hV x (hS hx)) hcls hlt
  have key : ∀ x ∈ V', ∀ y ∈ V', ∀ z ∈ V', x ≠ y → x ≠ z → y ≠ z → ¬ Fail3 pythia14m x y z := by
    intro x hx y hy z hz hxy hxz hyz hfail
    obtain ⟨t, ht, hne, hle⟩ := (fail3_iff_prompt pythia14m x y z).mp hfail
    exact absurd (h x hx y hy z hz hxy hxz hyz t ht hne) (not_lt.mpr hle)
  rcases hf with h1 | h1 | h1 | h1 | h1 | h1
  · exact key a (hS ha) b (hS hb) d (hS hd) hab had hbd h1
  · exact key a (hS ha) d (hS hd) b (hS hb) had hab (Ne.symm hbd) h1
  · exact key b (hS hb) a (hS ha) d (hS hd) (Ne.symm hab) hbd had h1
  · exact key b (hS hb) d (hS hd) a (hS ha) hbd (Ne.symm hab) (Ne.symm had) h1
  · exact key d (hS hd) a (hS ha) b (hS hb) (Ne.symm had) (Ne.symm hbd) hab h1
  · exact key d (hS hd) b (hS hb) a (hS ha) (Ne.symm hbd) (Ne.symm had) (Ne.symm hab) h1

/-- Unconditional, and trivial: `CON.PRO.ClaimAt n` is false for `n > 5000`, since `V` has 5,000 tokens.
Nothing else about `ClaimAt n` with `n ≥ 3` is proved unconditionally. -/
theorem pro_claimAt_large (n : ℕ) (hn : 5000 < n) : ¬ PRO.ClaimAt n := by
  rintro ⟨V', δ, hV, hcard, -⟩
  have h1 : V' ⊆ PRO.V.toFinset := fun x hx => List.mem_toFinset.mpr (hV x hx)
  have h2 := Finset.card_le_card h1
  have h3 := List.toFinset_card_le PRO.V
  have h4 : PRO.V.length = 5000 := PRO.V_length
  omega

end

end CON
