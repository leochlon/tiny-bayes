import Mathlib
import CON.Pythia
import CON.PRO.V

/-! # Induction on repeated sequences in pythia-14m: the claim and its normal form

`Claim` is the statement, over the exact real-arithmetic model `pythia14m` (`PRO.Pythia`).
`main` proves that `Claim` is equivalent to `NormalForm`: a statement without the margin `δ`, with
exactly 1,000 tokens, about the next-token logits of the prompts `[BOS, r₁, …, rₘ, r₁, …, r_k]`.
`Claim` itself is neither proved nor refuted here. `ClaimAt n` is the same statement with `n` tokens. -/

namespace CON.PRO

noncomputable section

/-- The repeated sequence `[BOS, r₁, …, rₘ, r₁, …, rₘ]`; BOS is token 0. -/
def repSeq (r : List ℕ) : List ℕ := 0 :: (r ++ r)

/-- Final output logit of token `t` at position `p` (0-based) when the model with parameters `θ`
runs on the whole sequence `toks`. -/
def logitAt (θ : Params) (toks : List ℕ) (p t : ℕ) : ℝ :=
  dot (θ.unemb t) (layerNorm θ.lnfg θ.lnfb ((hidden θ toks).getD p []))

/-- `r = [r₁, …, rₘ]` is a list of distinct tokens of `V'` with `3 ≤ m ≤ 8`. -/
def Admissible (V' : Finset ℕ) (r : List ℕ) : Prop :=
  r.Nodup ∧ (∀ t ∈ r, t ∈ V') ∧ 3 ≤ r.length ∧ r.length ≤ 8

/-- At the position of the second copy that holds `r_k` (`k` counted from 1, so position `m + k` of
`repSeq r`, counted from 0): the logit of `r_{k+1}` (which is `r.getD k 0`) minus the logit of `t`. -/
def gap (r : List ℕ) (k t : ℕ) : ℝ :=
  logitAt pythia14m (repSeq r) (r.length + k) (r.getD k 0)
    - logitAt pythia14m (repSeq r) (r.length + k) t

/-- The statement of the claim with `n` in place of 1,000: there are a set `V'` of at least `n` tokens
of `V` and a margin `δ > 0` such that for every list `r` of distinct tokens of `V'` with `3 ≤ m ≤ 8`
and every `k` with `2 ≤ k ≤ m - 1`, at the second-copy position holding `r_k` the logit of `r_{k+1}`
exceeds the logit of every other token `t < 50304` by at least `δ`. -/
def ClaimAt (n : ℕ) : Prop :=
  ∃ (V' : Finset ℕ) (δ : ℝ), (∀ t ∈ V', t ∈ V) ∧ n ≤ V'.card ∧ 0 < δ ∧
    ∀ r : List ℕ, Admissible V' r → ∀ k : ℕ, 2 ≤ k → k + 1 ≤ r.length →
      ∀ t : ℕ, t < 50304 → t ≠ r.getD k 0 → δ ≤ gap r k t

/-- **The claim**: at least 1,000 tokens. -/
def Claim : Prop := ClaimAt 1000

/-- `ClaimAt n` without the margin and with exactly `n` tokens, stated with the next-token logit
`logit` of the model: after the prompt `[BOS, r₁, …, rₘ, r₁, …, r_k]` the logit of
`r_{k+1}` is strictly the largest of the 50,304. -/
def NormalFormAt (n : ℕ) : Prop :=
  ∃ V' : Finset ℕ, (∀ t ∈ V', t ∈ V) ∧ V'.card = n ∧
    ∀ r : List ℕ, Admissible V' r → ∀ k : ℕ, 2 ≤ k → k + 1 ≤ r.length →
      ∀ t : ℕ, t < 50304 → t ≠ r.getD k 0 →
        logit pythia14m (0 :: (r ++ r.take k)) t < logit pythia14m (0 :: (r ++ r.take k)) (r.getD k 0)

/-- The normal form of the claim: exactly 1,000 tokens. -/
def NormalForm : Prop := NormalFormAt 1000

/-! ## Causality: logits at a position are the next-token logits of the initial segment -/

theorem getD_take_of_lt {α : Type} (l : List α) (n j : ℕ) (d : α) (h : j < n) :
    (l.take n).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem headOut_take (L : Layer) (U : List (List ℝ)) (n j h : ℕ) (hj : j < n) :
    headOut L (U.take n) j h = headOut L U j h := by
  have h1 : (U.take n).take (j + 1) = U.take (j + 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have h2 : (U.take n).getD j [] = U.getD j [] := getD_take_of_lt U n j [] hj
  simp only [headOut, h1, h2]

theorem attnOut_take (L : Layer) (U : List (List ℝ)) (n j : ℕ) (hj : j < n) :
    attnOut L (U.take n) j = attnOut L U j := by
  have key : ∀ h, headOut L (U.take n) j h = headOut L U j h := fun h => headOut_take L U n j h hj
  simp only [attnOut, key]

theorem layer_take (L : Layer) (H : List (List ℝ)) (n : ℕ) :
    (layer L H).take n = layer L (H.take n) := by
  unfold layer
  rw [← List.map_take, List.take_range, List.length_take]
  apply List.map_congr_left
  intro j hj
  have hj' : j < n := by
    have := List.mem_range.mp hj
    omega
  have e1 := attnOut_take L (H.map (layerNorm L.ln1g L.ln1b)) n j hj'
  have e2 := getD_take_of_lt H n j [] hj'
  simp only [List.map_take, e1, e2]

theorem foldl_layer_take (Ls : List Layer) (H : List (List ℝ)) (n : ℕ) :
    (Ls.foldl (fun H L => layer L H) H).take n = Ls.foldl (fun H L => layer L H) (H.take n) := by
  induction Ls generalizing H with
  | nil => rfl
  | cons L Ls ih => simp only [List.foldl_cons]; rw [ih, layer_take]

/-- The residual streams of an initial segment are the initial segment of the residual streams. -/
theorem hidden_take (θ : Params) (toks : List ℕ) (n : ℕ) :
    (hidden θ toks).take n = hidden θ (toks.take n) := by
  unfold hidden
  rw [foldl_layer_take, List.map_take]

/-- Causality: the logits at position `p` of a sequence are the next-token logits of its initial
segment of length `p + 1`. -/
theorem logitAt_eq_logit_take (θ : Params) (toks : List ℕ) (p t : ℕ) (hp : p < toks.length) :
    logitAt θ toks p t = logit θ (toks.take (p + 1)) t := by
  unfold logitAt logit lastHidden
  have hlen : (toks.take (p + 1)).length - 1 = p := by
    rw [List.length_take]; omega
  rw [hlen, ← hidden_take, getD_take_of_lt _ (p + 1) p [] (by omega)]

theorem repSeq_take (r : List ℕ) (k : ℕ) :
    (repSeq r).take (r.length + k + 1) = 0 :: (r ++ r.take k) := by
  simp [repSeq, List.take_append]

/-- The gap of the claim, as a difference of next-token logits after `[BOS, r₁, …, rₘ, r₁, …, r_k]`. -/
theorem gap_eq (r : List ℕ) (k t : ℕ) (hk : k + 1 ≤ r.length) :
    gap r k t = logit pythia14m (0 :: (r ++ r.take k)) (r.getD k 0)
      - logit pythia14m (0 :: (r ++ r.take k)) t := by
  have hp : r.length + k < (repSeq r).length := by
    simp [repSeq]; omega
  unfold gap
  rw [logitAt_eq_logit_take _ _ _ _ hp, logitAt_eq_logit_take _ _ _ _ hp, repSeq_take]

/-! ## The margin is free: finitely many cases -/

theorem finite_lists (s : Finset ℕ) (n : ℕ) :
    {r : List ℕ | r.length ≤ n ∧ ∀ t ∈ r, t ∈ s}.Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton ([] : List ℕ)) ?_
    rintro r ⟨h, -⟩
    have : r = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
    simp [this]
  | succ n ih =>
    refine Set.Finite.subset ((Set.finite_singleton ([] : List ℕ)).union
      (Set.Finite.image2 List.cons s.finite_toSet ih)) ?_
    rintro r ⟨h, hm⟩
    cases r with
    | nil => exact Or.inl rfl
    | cons a l =>
      refine Or.inr (Set.mem_image2.mpr ⟨a, ?_, l, ⟨?_, ?_⟩, rfl⟩)
      · exact Finset.mem_coe.mpr (hm a (by simp))
      · simpa using h
      · exact fun t ht => hm t (by simp [ht])

/-- The cases of the claim for a given `V'`: `(r, k, t)`. -/
def Cases (V' : Finset ℕ) : Set (List ℕ × ℕ × ℕ) :=
  {x | Admissible V' x.1 ∧ 2 ≤ x.2.1 ∧ x.2.1 + 1 ≤ x.1.length ∧ x.2.2 < 50304
    ∧ x.2.2 ≠ x.1.getD x.2.1 0}

theorem mem_cases (V' : Finset ℕ) (r : List ℕ) (k t : ℕ) :
    (r, k, t) ∈ Cases V' ↔ Admissible V' r ∧ 2 ≤ k ∧ k + 1 ≤ r.length ∧ t < 50304 ∧ t ≠ r.getD k 0 :=
  Iff.rfl

theorem cases_finite (V' : Finset ℕ) : (Cases V').Finite := by
  refine Set.Finite.subset
    ((finite_lists V' 8).prod ((Set.finite_Iio 9).prod (Set.finite_Iio 50304))) ?_
  rintro ⟨r, k, t⟩ hx
  obtain ⟨hr, -, hk', ht, -⟩ := (mem_cases V' r k t).mp hx
  refine Set.mem_prod.mpr ⟨⟨hr.2.2.2, hr.2.1⟩, Set.mem_prod.mpr ⟨?_, ?_⟩⟩
  · have := hr.2.2.2
    exact Set.mem_Iio.mpr (show k < 9 by omega)
  · exact Set.mem_Iio.mpr ht

theorem exists_margin {ι : Type} (T : Set ι) (hT : T.Finite) (f : ι → ℝ)
    (hf : ∀ x ∈ T, 0 < f x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T, δ ≤ f x := by
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, hx, hmin⟩ := Set.exists_min_image T f hT h
    exact ⟨f x, hf x hx, hmin⟩

/-- `V` has 5,000 tokens. -/
theorem V_length : V.length = 5000 := by decide +kernel

/-- The claim at any size is equivalent to its normal form. -/
theorem claimAt_iff_normalFormAt (n : ℕ) : ClaimAt n ↔ NormalFormAt n := by
  constructor
  · rintro ⟨V', δ, hV, hcard, hδ, h⟩
    obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq hcard
    refine ⟨W, fun t ht => hV t (hW ht), hWc, ?_⟩
    intro r hr k hk hk' t ht hne
    have hr' : Admissible V' r := ⟨hr.1, fun t ht => hW (hr.2.1 t ht), hr.2.2.1, hr.2.2.2⟩
    have h1 := h r hr' k hk hk' t ht hne
    rw [gap_eq r k t hk'] at h1
    linarith
  · rintro ⟨V', hV, hcard, h⟩
    obtain ⟨δ, hδ, hmin⟩ := exists_margin (Cases V') (cases_finite V')
      (fun x => gap x.1 x.2.1 x.2.2) (by
        rintro ⟨r, k, t⟩ hx
        obtain ⟨hr, hk, hk', ht, hne⟩ := (mem_cases V' r k t).mp hx
        have h1 := h r hr k hk hk' t ht hne
        show 0 < gap r k t
        rw [gap_eq r k t hk']
        linarith)
    exact ⟨V', δ, hV, hcard.ge, hδ, fun r hr k hk hk' t ht hne =>
      hmin (r, k, t) ((mem_cases V' r k t).mpr ⟨hr, hk, hk', ht, hne⟩)⟩

/-- The claim at a size implies the claim at every smaller size. -/
theorem claimAt_anti {n n' : ℕ} (hn : n' ≤ n) : ClaimAt n → ClaimAt n' := by
  rintro ⟨V', δ, hV, hcard, hδ, h⟩
  exact ⟨V', δ, hV, hn.trans hcard, hδ, h⟩

/-- **Main result: the claim is equivalent to its normal form.** The margin `δ` and "at least" carry
no content (there are finitely many sequences), and the logits read at positions of the full
sequence are the next-token logits of its initial segments (causal attention). This does not decide
`Claim`: it is neither proved nor refuted here. -/
theorem main : Claim ↔ NormalForm := claimAt_iff_normalFormAt 1000

/-- The smallest cases of the claim (`m = 3`, `k = 2`): if the claim holds, some 1,000 tokens of `V`
are such that after `[BOS, a, b, c, a, b]` the logit of `c` is strictly the largest, for every
ordered triple of distinct tokens `a, b, c` among them. -/
theorem claim_triples : Claim → ∃ V' : Finset ℕ, (∀ t ∈ V', t ∈ V) ∧ V'.card = 1000 ∧
    ∀ a ∈ V', ∀ b ∈ V', ∀ c ∈ V', a ≠ b → a ≠ c → b ≠ c → ∀ t : ℕ, t < 50304 → t ≠ c →
      logit pythia14m [0, a, b, c, a, b] t < logit pythia14m [0, a, b, c, a, b] c := by
  intro h
  obtain ⟨V', hV, hcard, hN⟩ := main.mp h
  refine ⟨V', hV, hcard, ?_⟩
  intro a ha b hb c hc hab hac hbc t ht hne
  have hadm : Admissible V' [a, b, c] := by
    refine ⟨?_, ?_, by simp, by simp⟩
    · simp [hab, hac, hbc]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  exact hN [a, b, c] hadm 2 (le_refl 2) (by simp) t ht hne

end

end CON.PRO
