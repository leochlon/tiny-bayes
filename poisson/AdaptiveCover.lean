import CellCover
namespace PinnCert

inductive CoverTree where
  | leaf : CoverTree
  | node : CoverTree → CoverTree → CoverTree → CoverTree → CoverTree
  deriving Repr, DecidableEq

def CoverTree.cells : CoverTree → Cell → List Cell
  | .leaf, b => [b]
  | .node a c d e, b =>
      ((a.cells b.child00 ++ c.cells b.child01) ++ d.cells b.child10) ++ e.cells b.child11

theorem CoverTree.covers (t : CoverTree) (b : Cell) {x y : ℝ} (hb : b.Contains x y) :
    ∃ c ∈ t.cells b, c.Contains x y := by
  induction t generalizing b x y with
  | leaf => exact ⟨b,by simp [cells],hb⟩
  | node a c d e ha hc hd he =>
    apply Cell.quad_sound b (fun x y => ∃ k ∈ (CoverTree.node a c d e).cells b, k.Contains x y)
      (fun u w h => by
        obtain ⟨k,hk,hkw⟩ := ha b.child00 h
        exact ⟨k,by simp only [cells,List.mem_append]; exact Or.inl (Or.inl (Or.inl hk)),hkw⟩)
      (fun u w h => by
        obtain ⟨k,hk,hkw⟩ := hc b.child01 h
        exact ⟨k,by simp only [cells,List.mem_append]; exact Or.inl (Or.inl (Or.inr hk)),hkw⟩)
      (fun u w h => by
        obtain ⟨k,hk,hkw⟩ := hd b.child10 h
        exact ⟨k,by simp only [cells,List.mem_append]; exact Or.inl (Or.inr hk),hkw⟩)
      (fun u w h => by
        obtain ⟨k,hk,hkw⟩ := he b.child11 h
        exact ⟨k,by simp only [cells,List.mem_append]; exact Or.inr hk,hkw⟩)
      x y hb

theorem CoverTree.bound_of_leaves (t : CoverTree) (b : Cell) (P : ℝ → ℝ → Prop)
    (h : ∀ c ∈ t.cells b, ∀ x y, c.Contains x y → P x y)
    {x y : ℝ} (hb : b.Contains x y) : P x y := by
  obtain ⟨c,hc,hxy⟩ := t.covers b hb
  exact h c hc x y hxy

#print axioms CoverTree.covers
end PinnCert
