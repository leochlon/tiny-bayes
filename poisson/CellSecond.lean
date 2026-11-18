import SecondOrder
namespace PinnCert
open Set
namespace Cell

theorem geometry (b : Cell) {x y : ℝ}
    (hc : b.xl ≤ b.cx ∧ b.cx ≤ b.xu ∧ b.yl ≤ b.cy ∧ b.cy ≤ b.yu)
    (hb : b.Contains x y) :
    (b.cx:ℝ)/S ∈ Icc ((b.xl:ℝ)/S) ((b.xu:ℝ)/S) ∧
    (b.cy:ℝ)/S ∈ Icc ((b.yl:ℝ)/S) ((b.yu:ℝ)/S) ∧
    |x-(b.cx:ℝ)/S| ≤ (b.hx:ℝ)/S ∧ |y-(b.cy:ℝ)/S| ≤ (b.hy:ℝ)/S := by
  have hcx : (b.cx:ℝ)/S ∈ Icc ((b.xl:ℝ)/S) ((b.xu:ℝ)/S) := by
    constructor <;> apply div_le_div_of_nonneg_right _ S_pos.le
    · exact_mod_cast hc.1
    · exact_mod_cast hc.2.1
  have hcy : (b.cy:ℝ)/S ∈ Icc ((b.yl:ℝ)/S) ((b.yu:ℝ)/S) := by
    constructor <;> apply div_le_div_of_nonneg_right _ S_pos.le
    · exact_mod_cast hc.2.2.1
    · exact_mod_cast hc.2.2.2
  have hdistx : |x-(b.cx:ℝ)/S| ≤ (b.hx:ℝ)/S := by
    have h1 : (b.cx:ℝ)-b.xl ≤ b.hx := by exact_mod_cast le_max_left (b.cx-b.xl) (b.xu-b.cx)
    have h2 : (b.xu:ℝ)-b.cx ≤ b.hx := by exact_mod_cast le_max_right (b.cx-b.xl) (b.xu-b.cx)
    apply abs_le.mpr
    constructor
    · have := div_le_div_of_nonneg_right h1 S_pos.le
      rw [sub_div] at this
      linarith [hb.1]
    · have := div_le_div_of_nonneg_right h2 S_pos.le
      rw [sub_div] at this
      linarith [hb.2.1]
  have hdisty : |y-(b.cy:ℝ)/S| ≤ (b.hy:ℝ)/S := by
    have h1 : (b.cy:ℝ)-b.yl ≤ b.hy := by exact_mod_cast le_max_left (b.cy-b.yl) (b.yu-b.cy)
    have h2 : (b.yu:ℝ)-b.cy ≤ b.hy := by exact_mod_cast le_max_right (b.cy-b.yl) (b.yu-b.cy)
    apply abs_le.mpr
    constructor
    · have := div_le_div_of_nonneg_right h1 S_pos.le
      rw [sub_div] at this
      linarith [hb.2.2.1]
    · have := div_le_div_of_nonneg_right h2 S_pos.le
      rw [sub_div] at this
      linarith [hb.2.2.2]
  exact ⟨hcx,hcy,hdistx,hdisty⟩

def secondCheck (e : Expr) (b : Cell) (R : ℤ) : Bool :=
  let ex := e.ndiff false
  let ey := e.ndiff true
  let v := e.interval (cst b.cx) (cst b.cy)
  let gx := ex.interval (cst b.cx) (cst b.cy)
  let gy := ey.interval (cst b.cx) (cst b.cy)
  let xx := (ex.ndiff false).interval b.X b.Y
  let xy := (ex.ndiff true).interval b.X b.Y
  let yx := (ey.ndiff false).interval b.X b.Y
  let yy := (ey.ndiff true).interval b.X b.Y
  (v.ok && gx.ok && gy.ok) && (xx.ok && xy.ok && yx.ok && yy.ok) &&
    decide (b.xl ≤ b.cx ∧ b.cx ≤ b.xu ∧ b.yl ≤ b.cy ∧ b.cy ≤ b.yu) &&
    decide (0 ≤ gx.mag ∧ 0 ≤ gy.mag ∧ 0 ≤ xx.mag ∧ 0 ≤ xy.mag ∧ 0 ≤ yx.mag ∧ 0 ≤ yy.mag) &&
    decide (2*S*S*v.mag+2*S*(gx.mag*b.hx+gy.mag*b.hy)+
      xx.mag*b.hx*b.hx+xy.mag*b.hy*b.hx+yx.mag*b.hx*b.hy+yy.mag*b.hy*b.hy ≤ 2*R*S*S)

theorem secondCheck_sound (e : Expr) (b : Cell) (R : ℤ)
    (h : secondCheck e b R = true) {x y : ℝ} (hb : b.Contains x y) :
    |e.eval x y| ≤ (R:ℝ)/S := by
  simp only [secondCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hv,hh⟩,hc⟩,hn⟩,hnum⟩ := h
  obtain ⟨hcx,hcy,hdistx,hdisty⟩ := b.geometry hc hb
  let ex := e.ndiff false
  let ey := e.ndiff true
  let v := e.interval (cst b.cx) (cst b.cy)
  let gx := ex.interval (cst b.cx) (cst b.cy)
  let gy := ey.interval (cst b.cx) (cst b.cy)
  let xx := (ex.ndiff false).interval b.X b.Y
  let xy := (ex.ndiff true).interval b.X b.Y
  let yx := (ey.ndiff false).interval b.X b.Y
  let yy := (ey.ndiff true).interval b.X b.Y
  have hgx : 0 ≤ (gx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.1) S_pos.le
  have hgy : 0 ≤ (gy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.1) S_pos.le
  have hxx : 0 ≤ (xx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.1) S_pos.le
  have hxy : 0 ≤ (xy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.1) S_pos.le
  have hyx : 0 ≤ (yx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.2.1) S_pos.le
  have hyy : 0 ≤ (yy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2.2.2.2.2) S_pos.le
  have hm := rectangle_taylor2 e hcx hcy ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩
    (memAt_abs (e.interval_sound (memCst b.cx) (memCst b.cy)) hv.1.1)
    (memAt_abs (ex.interval_sound (memCst b.cx) (memCst b.cy)) hv.1.2)
    (memAt_abs (ey.interval_sound (memCst b.cx) (memCst b.cy)) hv.2)
    (fun u hu w hw => memAt_abs ((ex.ndiff false).interval_sound (b.memX hu) (b.memY hw)) hh.1.1.1)
    (fun u hu w hw => memAt_abs ((ex.ndiff true).interval_sound (b.memX hu) (b.memY hw)) hh.1.1.2)
    (fun u hu w hw => memAt_abs ((ey.ndiff false).interval_sound (b.memX hu) (b.memY hw)) hh.1.2)
    (fun u hu w hw => memAt_abs ((ey.ndiff true).interval_sound (b.memX hu) (b.memY hw)) hh.2)
    hgx hgy hxx hxy hyx hyy hdistx hdisty
  apply hm.trans
  have hn' : (2:ℝ)*S*S*v.mag+2*S*(gx.mag*b.hx+gy.mag*b.hy)+
      xx.mag*b.hx*b.hx+xy.mag*b.hy*b.hx+yx.mag*b.hx*b.hy+yy.mag*b.hy*b.hy ≤ 2*R*S*S := by
    exact_mod_cast hnum
  have hs : (0:ℝ) < 2*(S:ℝ)^3 := mul_pos (by norm_num) (pow_pos S_pos _)
  apply (mul_le_mul_iff_left₀ hs).mp
  convert hn' using 1 <;> dsimp [v,gx,gy,xx,xy,yx,yy,ex,ey] <;> field_simp [S_pos.ne'] <;> ring

#check secondCheck_sound
#print axioms secondCheck_sound
end Cell
end PinnCert
