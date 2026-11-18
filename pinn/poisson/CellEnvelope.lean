import CellSecond
namespace PinnCert
open Set
namespace Cell
def secondEnvelopeCheck (b : Cell) (R : ℤ) (v gx gy xx xy yx yy : Iv) : Bool :=
  (v.ok && gx.ok && gy.ok) && (xx.ok && xy.ok && yx.ok && yy.ok) &&
    decide (b.xl ≤ b.cx ∧ b.cx ≤ b.xu ∧ b.yl ≤ b.cy ∧ b.cy ≤ b.yu) &&
    decide (0 ≤ gx.mag ∧ 0 ≤ gy.mag ∧ 0 ≤ xx.mag ∧ 0 ≤ xy.mag ∧ 0 ≤ yx.mag ∧ 0 ≤ yy.mag) &&
    decide (2*S*S*v.mag+2*S*(gx.mag*b.hx+gy.mag*b.hy)+
      xx.mag*b.hx*b.hx+xy.mag*b.hy*b.hx+yx.mag*b.hx*b.hy+yy.mag*b.hy*b.hy ≤ 2*R*S*S)

theorem secondEnvelope_sound (e : Expr) (b : Cell) (R : ℤ) (v gx gy xx xy yx yy : Iv)
    (hv0 : memAt S (e.eval ((b.cx:ℝ)/S) ((b.cy:ℝ)/S)) v)
    (hgx0 : memAt S ((e.ndiff false).eval ((b.cx:ℝ)/S) ((b.cy:ℝ)/S)) gx)
    (hgy0 : memAt S ((e.ndiff true).eval ((b.cx:ℝ)/S) ((b.cy:ℝ)/S)) gy)
    (hxx0 : ∀ u w, b.Contains u w → memAt S (((e.ndiff false).ndiff false).eval u w) xx)
    (hxy0 : ∀ u w, b.Contains u w → memAt S (((e.ndiff false).ndiff true).eval u w) xy)
    (hyx0 : ∀ u w, b.Contains u w → memAt S (((e.ndiff true).ndiff false).eval u w) yx)
    (hyy0 : ∀ u w, b.Contains u w → memAt S (((e.ndiff true).ndiff true).eval u w) yy)
    (h : secondEnvelopeCheck b R v gx gy xx xy yx yy = true)
    {x y : ℝ} (hb : b.Contains x y) : |e.eval x y| ≤ (R:ℝ)/S := by
  simp only [secondEnvelopeCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hv,hh⟩,hc⟩,hn⟩,hnum⟩ := h
  obtain ⟨hcx,hcy,hdistx,hdisty⟩ := b.geometry hc hb
  have hgx : 0 ≤ (gx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.1) S_pos.le
  have hgy : 0 ≤ (gy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.1) S_pos.le
  have hxx : 0 ≤ (xx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.1) S_pos.le
  have hxy : 0 ≤ (xy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.1) S_pos.le
  have hyx : 0 ≤ (yx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.2.1) S_pos.le
  have hyy : 0 ≤ (yy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.2.2) S_pos.le
  have hm := rectangle_taylor2 e hcx hcy ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩
    (memAt_abs hv0 hv.1.1)
    (memAt_abs hgx0 hv.1.2)
    (memAt_abs hgy0 hv.2)
    (fun u hu w hw => memAt_abs (hxx0 u w ⟨hu.1,hu.2,hw.1,hw.2⟩) hh.1.1.1)
    (fun u hu w hw => memAt_abs (hxy0 u w ⟨hu.1,hu.2,hw.1,hw.2⟩) hh.1.1.2)
    (fun u hu w hw => memAt_abs (hyx0 u w ⟨hu.1,hu.2,hw.1,hw.2⟩) hh.1.2)
    (fun u hu w hw => memAt_abs (hyy0 u w ⟨hu.1,hu.2,hw.1,hw.2⟩) hh.2)
    hgx hgy hxx hxy hyx hyy hdistx hdisty
  apply hm.trans
  have hn' : (2:ℝ)*S*S*v.mag+2*S*(gx.mag*b.hx+gy.mag*b.hy)+
      xx.mag*b.hx*b.hx+xy.mag*b.hy*b.hx+yx.mag*b.hx*b.hy+yy.mag*b.hy*b.hy ≤ 2*R*S*S := by
    exact_mod_cast hnum
  have hs : (0:ℝ) < 2*(S:ℝ)^3 := mul_pos (by norm_num) (pow_pos S_pos _)
  apply (mul_le_mul_iff_left₀ hs).mp
  convert hn' using 1 <;> field_simp [S_pos.ne'] <;> ring

#print axioms secondEnvelope_sound
end Cell
end PinnCert
