import Mathlib
import PRO.Model

/-! The module `CON.Induction` of the first version of `upper_bound/`, under the namespace `PRO.Opp`. -/

/-! # The induction statement for a network of pythia-14m's shape, and how it is refuted

Everything here is for arbitrary parameters `θ`; `CON.Main` instantiates `θ` with the real weights.

Positions are 0-based. The input is `repSeq r = [BOS, r₁, …, rₘ, r₁, …, rₘ]` with `BOS = 0`; the token
`r_k` of the second copy sits at position `m + k`, and `r_{k+1}` is `r.getD k 0`. -/

namespace PRO

namespace Opp

noncomputable section

/-- Final output logit of token `t` at position `p` of the input `toks`: row `t` of the unembedding
dotted with the final LayerNorm of the residual stream at position `p` after the last layer. -/
def logitAt (θ : Params) (toks : List ℕ) (p t : ℕ) : ℝ :=
  dot (θ.unemb t) (layerNorm θ.lnfg θ.lnfb ((hidden θ toks).getD p []))

/-- The repeated sequence `[BOS, r₁, …, rₘ, r₁, …, rₘ]`; BOS is token 0. -/
def repSeq (r : List ℕ) : List ℕ := 0 :: (r ++ r)

/-- "The model performs induction on every repeated sequence over `V'` with margin `δ`":
for every list `r` of distinct tokens of `V'` with `3 ≤ m ≤ 8` (`m = r.length`) and every `k` with
`2 ≤ k ≤ m - 1`, at the position `m + k` holding `r_k` in the second copy, the logit of
`r_{k+1} = r.getD k 0` exceeds the logit of every other token `t < 50304` by at least `δ`. -/
def InductionOn (θ : Params) (V' : Finset ℕ) (δ : ℝ) : Prop :=
  ∀ r : List ℕ, r.Nodup → (∀ x ∈ r, x ∈ V') → 3 ≤ r.length → r.length ≤ 8 →
    ∀ k : ℕ, 2 ≤ k → k ≤ r.length - 1 →
      ∀ t : ℕ, t < 50304 → t ≠ r.getD k 0 →
        logitAt θ (repSeq r) (r.length + k) t + δ ≤ logitAt θ (repSeq r) (r.length + k) (r.getD k 0)

/-- The model fails on the repeated triple `(x, y, z)`: at the second `y` (position 5 of
`[0, x, y, z, x, y, z]`, the case `m = 3`, `k = 2`) some token other than `z` has a logit at least
that of `z`. -/
def Fail3 (θ : Params) (x y z : ℕ) : Prop :=
  ∃ t : ℕ, t < 50304 ∧ t ≠ z ∧
    logitAt θ [0, x, y, z, x, y, z] 5 z ≤ logitAt θ [0, x, y, z, x, y, z] 5 t

/-- The model fails on at least one of the six orders of the three tokens. -/
def FailSome (θ : Params) (a b c : ℕ) : Prop :=
  Fail3 θ a b c ∨ Fail3 θ a c b ∨ Fail3 θ b a c ∨ Fail3 θ b c a ∨ Fail3 θ c a b ∨ Fail3 θ c b a

/-- One failing triple rules out every `V'` that contains its three tokens, for every margin. -/
theorem fail3_excludes' (θ : Params) {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) {x y z : ℕ}
    (hx : x ∈ V') (hy : y ∈ V') (hz : z ∈ V') (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf : Fail3 θ x y z) : ¬ InductionOn θ V' δ := by
  intro h
  obtain ⟨t, ht, htz, hle⟩ := hf
  have h1 := h [x, y, z] (by simp [hxy, hxz, hyz]) (by simp [hx, hy, hz]) (by simp) (by simp)
    2 (by norm_num) (by simp) t ht (by simpa using htz)
  have h2 : logitAt θ [0, x, y, z, x, y, z] 5 t + δ ≤ logitAt θ [0, x, y, z, x, y, z] 5 z := h1
  linarith

/-- The residual streams depend on the tokens only through their input embeddings. -/
theorem hidden_congr (θ : Params) {s t : List ℕ} (h : s.map θ.emb = t.map θ.emb) :
    hidden θ s = hidden θ t := by
  unfold hidden
  rw [h]

/-- Two tokens with the same input embedding cannot both belong to `V'` (given two further tokens
of `V'`): swapping them as `r₃` leaves every logit unchanged, but the statement asks for opposite
orders of their two logits. Holds for every parameter assignment. -/
theorem twin_excludes' (θ : Params) {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) {x y a b : ℕ}
    (hx : x ∈ V') (hy : y ∈ V') (ha : a ∈ V') (hb : b ∈ V')
    (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (hav : a < 50304) (hbv : b < 50304) (he : θ.emb a = θ.emb b) : ¬ InductionOn θ V' δ := by
  intro h
  have h1 := h [x, y, a] (by simp [hxy, hxa, hya]) (by simp [hx, hy, ha]) (by simp) (by simp)
    2 (by norm_num) (by simp) b hbv (by simpa using hab.symm)
  have h2 := h [x, y, b] (by simp [hxy, hxb, hyb]) (by simp [hx, hy, hb]) (by simp) (by simp)
    2 (by norm_num) (by simp) a hav (by simpa using hab)
  have e : hidden θ (repSeq [x, y, a]) = hidden θ (repSeq [x, y, b]) :=
    hidden_congr θ (by simp [repSeq, he])
  have e1 : ∀ t, logitAt θ (repSeq [x, y, a]) 5 t = logitAt θ (repSeq [x, y, b]) 5 t := by
    intro t
    unfold logitAt
    rw [e]
  have h1' : logitAt θ (repSeq [x, y, a]) 5 b + δ ≤ logitAt θ (repSeq [x, y, a]) 5 a := h1
  have h2' : logitAt θ (repSeq [x, y, b]) 5 a + δ ≤ logitAt θ (repSeq [x, y, b]) 5 b := h2
  linarith [e1 a, e1 b]

/-- The model fails on some repeated sequence over `S`: there are a list `r` of distinct tokens of
`S` with `3 ≤ m ≤ 8`, a `k` with `2 ≤ k ≤ m - 1` and a token `t ≠ r_{k+1}` of the vocabulary whose
logit at the second `r_k` is at least the logit of `r_{k+1}`. -/
def FailsOn (θ : Params) (S : Finset ℕ) : Prop :=
  ∃ r : List ℕ, r.Nodup ∧ (∀ x ∈ r, x ∈ S) ∧ 3 ≤ r.length ∧ r.length ≤ 8 ∧
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ r.length - 1 ∧
      ∃ t : ℕ, t < 50304 ∧ t ≠ r.getD k 0 ∧
        logitAt θ (repSeq r) (r.length + k) (r.getD k 0) ≤ logitAt θ (repSeq r) (r.length + k) t

/-- A failing sequence over `S` rules out every `V'` containing `S`, for every positive margin. -/
theorem failsOn_excludes' (θ : Params) {S V' : Finset ℕ} {δ : ℝ} (hf : FailsOn θ S) (hS : S ⊆ V')
    (hδ : 0 < δ) : ¬ InductionOn θ V' δ := by
  obtain ⟨r, hnd, hmem, h3, h8, k, hk2, hkm, t, ht, hne, hle⟩ := hf
  intro h
  have h1 := h r hnd (fun x hx => hS (hmem x hx)) h3 h8 k hk2 hkm t ht hne
  linarith

/-- A failing triple is a failing sequence over its three tokens. -/
theorem fail3_failsOn (θ : Params) {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf : Fail3 θ x y z) : FailsOn θ {x, y, z} := by
  obtain ⟨t, ht, htz, hle⟩ := hf
  exact ⟨[x, y, z], by simp [hxy, hxz, hyz], by simp, by simp, by simp, 2, by norm_num, by simp,
    t, ht, by simpa using htz, hle⟩

/-- Pigeonhole refutation. If the tokens are split into `N` classes by `f`, and the model fails on
some repeated sequence over every `j + 1` tokens of `V'` lying in one class, then induction fails on
every `V'` with more than `N * j` tokens, for every positive margin. -/
theorem classes_exclude' (θ : Params) (f : ℕ → ℕ) (N j : ℕ) (hf : ∀ a, f a < N)
    {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (hcard : N * j < V'.card)
    (hfail : ∀ S : Finset ℕ, S ⊆ V' → S.card = j + 1 → (∀ x ∈ S, ∀ y ∈ S, f x = f y) →
      FailsOn θ S) : ¬ InductionOn θ V' δ := by
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := V') (t := Finset.range N) (f := f) (n := j)
    (fun a _ => Finset.mem_range.mpr (hf a)) (by simpa using hcard)
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hy)
  have hSV : S ⊆ V' := hS.trans (Finset.filter_subset _ _)
  have hcls : ∀ x ∈ S, ∀ z ∈ S, f x = f z := by
    intro x hx z hz
    rw [(Finset.mem_filter.mp (hS hx)).2, (Finset.mem_filter.mp (hS hz)).2]
  exact failsOn_excludes' θ (hfail S hSV hSc hcls) hSV hδ

/-- Pigeonhole refutation with capacities. If the tokens are split into `N` classes by `f`, class `c`
has capacity `cap c` (the model fails on some repeated sequence over every set of more than `cap c`
tokens of `V'` in class `c`), and `V'` has more tokens than the capacities add up to, then induction
fails on `V'`, for every positive margin. -/
theorem capacities_exclude' (θ : Params) (f : ℕ → ℕ) (N : ℕ) (cap : ℕ → ℕ) (hf : ∀ a, f a < N)
    {V' : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (hcard : ∑ c ∈ Finset.range N, cap c < V'.card)
    (hfail : ∀ (c : ℕ) (S : Finset ℕ), S ⊆ V' → (∀ x ∈ S, f x = c) → cap c < S.card →
      FailsOn θ S) : ¬ InductionOn θ V' δ := by
  intro h
  have hle : ∀ c ∈ Finset.range N, (V'.filter (fun x => f x = c)).card ≤ cap c := by
    intro c _
    by_contra hlt
    exact failsOn_excludes' θ (hfail c _ (Finset.filter_subset _ _)
      (fun x hx => (Finset.mem_filter.mp hx).2) (not_le.mp hlt)) (Finset.filter_subset _ _) hδ h
  have hsum : V'.card = ∑ c ∈ Finset.range N, (V'.filter (fun x => f x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.mpr (hf x))
  exact lt_irrefl _ (lt_of_lt_of_le hcard (hsum.le.trans (Finset.sum_le_sum hle)))

/-- The finitely many instances `(r, k, t)` of the statement over `V'`. -/
def instances (V' : Finset ℕ) : Set (List ℕ × ℕ × ℕ) :=
  {i | (i.1.length ≤ 8 ∧ ∀ x ∈ i.1, x ∈ V') ∧ i.2.1 < 9 ∧ i.2.2 < 50304 ∧
    i.1.Nodup ∧ 3 ≤ i.1.length ∧ 2 ≤ i.2.1 ∧ i.2.1 ≤ i.1.length - 1 ∧ i.2.2 ≠ i.1.getD i.2.1 0}

/-- The gap between the logit of `r_{k+1}` and the logit of `t` for the instance `(r, k, t)`. -/
def gap (θ : Params) (i : List ℕ × ℕ × ℕ) : ℝ :=
  logitAt θ (repSeq i.1) (i.1.length + i.2.1) (i.1.getD i.2.1 0)
    - logitAt θ (repSeq i.1) (i.1.length + i.2.1) i.2.2

theorem instances_finite (V' : Finset ℕ) : (instances V').Finite := by
  have hL : {r : List ℕ | r.length ≤ 8 ∧ ∀ x ∈ r, x ∈ V'}.Finite := by
    have h1 : {l : List {y // y ∈ V'} | l.length ≤ 8}.Finite := List.finite_length_le _ 8
    refine (h1.image (List.map Subtype.val)).subset ?_
    rintro r ⟨hr8, hrm⟩
    refine ⟨r.attach.map (fun x => (⟨x.1, hrm x.1 x.2⟩ : {y // y ∈ V'})), ?_, ?_⟩
    · simpa using hr8
    · rw [List.map_map]
      exact List.attach_map_subtype_val r
  refine (hL.prod ((Set.finite_lt_nat 9).prod (Set.finite_lt_nat 50304))).subset ?_
  rintro ⟨r, k, t⟩ ⟨h1, h2, h3, -⟩
  exact Set.mk_mem_prod h1 (Set.mk_mem_prod h2 h3)

/-- The margin plays no role: a positive margin exists for `V'` exactly when no repeated sequence
over `V'` fails (the instances are finitely many, so the smallest gap is a margin). -/
theorem exists_margin_iff' (θ : Params) (V' : Finset ℕ) :
    (∃ δ : ℝ, 0 < δ ∧ InductionOn θ V' δ) ↔ ¬ FailsOn θ V' := by
  constructor
  · rintro ⟨δ, hδ, h⟩ hf
    exact failsOn_excludes' θ hf (Finset.Subset.refl _) hδ h
  · intro hnf
    have hpos : ∀ i ∈ instances V', 0 < gap θ i := by
      rintro ⟨r, k, t⟩ ⟨⟨h8, hm⟩, -, ht, hnd, h3, hk2, hkm, hne⟩
      by_contra hle
      have e : gap θ (r, k, t) = logitAt θ (repSeq r) (r.length + k) (r.getD k 0)
          - logitAt θ (repSeq r) (r.length + k) t := rfl
      exact hnf ⟨r, hnd, hm, h3, h8, k, hk2, hkm, t, ht, hne, by linarith [not_lt.mp hle]⟩
    have hmem : ∀ (r : List ℕ) (k t : ℕ), r.Nodup → (∀ x ∈ r, x ∈ V') → 3 ≤ r.length →
        r.length ≤ 8 → 2 ≤ k → k ≤ r.length - 1 → t < 50304 → t ≠ r.getD k 0 →
        (r, k, t) ∈ instances V' := by
      intro r k t hnd hm h3 h8 hk2 hkm ht hne
      exact ⟨⟨h8, hm⟩, (show k < 9 by omega), ht, hnd, h3, hk2, hkm, hne⟩
    rcases Set.eq_empty_or_nonempty (instances V') with hE | hE
    · refine ⟨1, one_pos, ?_⟩
      intro r hnd hm h3 h8 k hk2 hkm t ht hne
      have h := hmem r k t hnd hm h3 h8 hk2 hkm ht hne
      rw [hE] at h
      exact absurd h (Set.notMem_empty _)
    · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image (instances V') (gap θ) (instances_finite V') hE
      refine ⟨gap θ a, hpos a ha, ?_⟩
      intro r hnd hm h3 h8 k hk2 hkm t ht hne
      have h := hmin (r, k, t) (hmem r k t hnd hm h3 h8 hk2 hkm ht hne)
      have e : gap θ (r, k, t) = logitAt θ (repSeq r) (r.length + k) (r.getD k 0)
          - logitAt θ (repSeq r) (r.length + k) t := rfl
      linarith

end

end Opp

end PRO
