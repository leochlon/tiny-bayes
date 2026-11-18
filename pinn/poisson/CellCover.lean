import CellMVT

namespace PinnCert.Cell
def child00 (b : Cell) : Cell := ⟨b.xl,b.cx,b.yl,b.cy⟩
def child01 (b : Cell) : Cell := ⟨b.xl,b.cx,b.cy,b.yu⟩
def child10 (b : Cell) : Cell := ⟨b.cx,b.xu,b.yl,b.cy⟩
def child11 (b : Cell) : Cell := ⟨b.cx,b.xu,b.cy,b.yu⟩

/-- Exact four-child cover, including every shared edge and every exterior edge. -/
theorem quad_sound (b : Cell) (P : ℝ → ℝ → Prop)
    (h00 : ∀ x y, b.child00.Contains x y → P x y)
    (h01 : ∀ x y, b.child01.Contains x y → P x y)
    (h10 : ∀ x y, b.child10.Contains x y → P x y)
    (h11 : ∀ x y, b.child11.Contains x y → P x y)
    (x y : ℝ) (hb : b.Contains x y) : P x y := by
  by_cases hx : x ≤ (b.cx:ℝ)/S
  · by_cases hy : y ≤ (b.cy:ℝ)/S
    · exact h00 x y ⟨hb.1,hx,hb.2.2.1,hy⟩
    · exact h01 x y ⟨hb.1,hx,(lt_of_not_ge hy).le,hb.2.2.2⟩
  · by_cases hy : y ≤ (b.cy:ℝ)/S
    · exact h10 x y ⟨(lt_of_not_ge hx).le,hb.2.1,hb.2.2.1,hy⟩
    · exact h11 x y ⟨(lt_of_not_ge hx).le,hb.2.1,(lt_of_not_ge hy).le,hb.2.2.2⟩

#check quad_sound
#print axioms quad_sound
end PinnCert.Cell
