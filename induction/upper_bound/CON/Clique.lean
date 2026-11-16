import Mathlib

/-! # An exhaustive search over sets of positions, and its soundness

`mx mask n []` bounds the size of every set of positions below `n` all of whose triples `i < j < l`
have their bit set in `mask` (`mx_sound`, `clique_bound`). The kernel evaluates `mx` on literal masks. -/

namespace CON

/-- Index of the triple of positions `i < j < l` (combinatorial number system). -/
def tidx (i j l : ℕ) : ℕ := l * (l - 1) * (l - 2) / 6 + j * (j - 1) / 2 + i

/-- The bit of `mask` for the triple of positions `i < j < l`. -/
def tbit (mask i j l : ℕ) : Bool := Nat.testBit mask (tidx i j l)

/-- Position `k` may join the positions `s`: every triple `k < a < b` with `a, b` in `s` has its bit set. -/
def okExt (mask k : ℕ) (s : List ℕ) : Bool :=
  s.all fun a => s.all fun b => if k < a ∧ a < b then tbit mask k a b else true

/-- Exhaustive search, positions `k - 1, …, 0` in turn, each skipped or (when `okExt` allows) added. -/
def mx (mask : ℕ) : ℕ → List ℕ → ℕ
  | 0, s => s.length
  | k + 1, s => max (mx mask k s) (if okExt mask k s then mx mask k (k :: s) else 0)

/-- Every triple `i < j < l` of `A` has its bit set. -/
def Clq (mask : ℕ) (A : Finset ℕ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ l ∈ A, i < j → j < l → tbit mask i j l = true

theorem okExt_of_clq {mask k : ℕ} {s : List ℕ} {A : Finset ℕ} (hA : Clq mask A) (hk : k ∈ A)
    (hs : ∀ a ∈ s, a ∈ A) : okExt mask k s = true := by
  unfold okExt
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  by_cases h : k < a ∧ a < b
  · rw [if_pos h]
    exact hA k hk a (hs a ha) b (hs b hb) h.1 h.2
  · rw [if_neg h]

theorem mx_succ (mask k : ℕ) (s : List ℕ) :
    mx mask (k + 1) s = max (mx mask k s) (if okExt mask k s then mx mask k (k :: s) else 0) := rfl

theorem mx_sound (mask : ℕ) : ∀ (k : ℕ) (s : List ℕ) (U : Finset ℕ), U ⊆ Finset.range k →
    Clq mask (U ∪ s.toFinset) → (U ∪ s.toFinset).card ≤ mx mask k s := by
  intro k
  induction k with
  | zero =>
    intro s U hU _
    have hU0 : U = ∅ := by simpa using hU
    subst hU0
    have h := List.toFinset_card_le s
    simpa [mx] using h
  | succ k ih =>
    intro s U hU hclq
    by_cases hk : k ∈ U
    · have hok : okExt mask k s = true :=
        okExt_of_clq hclq (Finset.mem_union_left _ hk)
          (fun a ha => Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
      have hset : U.erase k ∪ (k :: s).toFinset = U ∪ s.toFinset := by
        ext x
        simp only [Finset.mem_union, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert,
          List.mem_toFinset]
        constructor
        · rintro (⟨_, h⟩ | h | h)
          · exact Or.inl h
          · exact Or.inl (h ▸ hk)
          · exact Or.inr h
        · rintro (h | h)
          · by_cases hx : x = k
            · exact Or.inr (Or.inl hx)
            · exact Or.inl ⟨hx, h⟩
          · exact Or.inr (Or.inr h)
      have hsub : U.erase k ⊆ Finset.range k := by
        intro x hx
        have h1 := Finset.mem_erase.mp hx
        have h2 := Finset.mem_range.mp (hU h1.2)
        have h3 := h1.1
        exact Finset.mem_range.mpr (by omega)
      have h := ih (k :: s) (U.erase k) hsub (by rw [hset]; exact hclq)
      rw [hset] at h
      rw [mx_succ, if_pos hok]
      exact le_max_of_le_right h
    · have hsub : U ⊆ Finset.range k := by
        intro x hx
        have h2 := Finset.mem_range.mp (hU hx)
        have h3 : x ≠ k := fun e => hk (e ▸ hx)
        exact Finset.mem_range.mpr (by omega)
      have h := ih s U hsub hclq
      rw [mx_succ]
      exact le_max_of_le_left h

/-- If the search stays within `cap`, every set of more than `cap` positions below `n` contains a
triple `i < j < l` whose bit is clear. -/
theorem clique_bound {mask n cap : ℕ} (h : mx mask n [] ≤ cap) {U : Finset ℕ}
    (hU : U ⊆ Finset.range n) (hc : cap < U.card) :
    ∃ i ∈ U, ∃ j ∈ U, ∃ l ∈ U, i < j ∧ j < l ∧ tbit mask i j l = false := by
  by_contra hno
  have hclq : Clq mask (U ∪ ([] : List ℕ).toFinset) := by
    intro i hi j hj l hl hij hjl
    have hi' : i ∈ U := by simpa using hi
    have hj' : j ∈ U := by simpa using hj
    have hl' : l ∈ U := by simpa using hl
    by_contra hb
    exact hno ⟨i, hi', j, hj', l, hl', hij, hjl, by simpa using hb⟩
  have h1 := mx_sound mask n [] U hU hclq
  have h2 : (U ∪ ([] : List ℕ).toFinset).card = U.card := by simp
  omega

end CON
