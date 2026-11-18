import ExprNormalize
import Mathlib.Analysis.Calculus.MeanValue

namespace PinnCert
open Set

theorem rectangle_mvt (f fx fy : ℝ → ℝ → ℝ)
    (hdx : ∀ x y, HasDerivAt (fun t => f t y) (fx x y) x)
    (hdy : ∀ x y, HasDerivAt (fun t => f x t) (fy x y) y)
    {a b c d cx cy x y A Bx By hx hy : ℝ}
    (hcx : cx ∈ Icc a b) (hcy : cy ∈ Icc c d)
    (hxbox : x ∈ Icc a b) (hybox : y ∈ Icc c d)
    (hcenter : |f cx cy| ≤ A)
    (hfx : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |fx u v| ≤ Bx)
    (hfy : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |fy u v| ≤ By)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hdistx : |x-cx| ≤ hx) (hdisty : |y-cy| ≤ hy) :
    |f x y| ≤ A+Bx*hx+By*hy := by
  have mx := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hdx u y).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hfx u hu y hybox) hcx hxbox
  have my := (convex_Icc c d).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hdy cx v).hasDerivWithinAt)
    (fun v hv => by simpa only [Real.norm_eq_abs] using hfy cx hcx v hv) hcy hybox
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at mx my
  have ex := mx.trans (mul_le_mul_of_nonneg_left hdistx hBx)
  have ey := my.trans (mul_le_mul_of_nonneg_left hdisty hBy)
  have he : f x y = (f x y-f cx y)+(f cx y-f cx cy)+f cx cy := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by
    have h := abs_add_le (f x y-f cx y) (f cx y-f cx cy)
    linarith)

def Iv.mag (I : Iv) : ℤ := max (-I.lo) I.hi

theorem memAt_abs {z : ℝ} {I : Iv} (hz : memAt S z I) (hok : I.ok=true) :
    |z| ≤ (I.mag:ℝ)/S := by
  obtain ⟨hl,hu⟩ := hz hok
  have hm1 : -(I.lo:ℝ) ≤ I.mag := by exact_mod_cast le_max_left (-I.lo) I.hi
  have hm2 : (I.hi:ℝ) ≤ I.mag := by exact_mod_cast le_max_right (-I.lo) I.hi
  rw [le_div_iff₀ S_pos,← abs_of_pos S_pos,← abs_mul]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

structure Cell where
  xl : ℤ
  xu : ℤ
  yl : ℤ
  yu : ℤ
  deriving Repr, DecidableEq

namespace Cell
def X (b : Cell) : Iv := ⟨b.xl,b.xu,true⟩
def Y (b : Cell) : Iv := ⟨b.yl,b.yu,true⟩
def cx (b : Cell) : ℤ := (b.xl+b.xu)/2
def cy (b : Cell) : ℤ := (b.yl+b.yu)/2
def hx (b : Cell) : ℤ := max (b.cx-b.xl) (b.xu-b.cx)
def hy (b : Cell) : ℤ := max (b.cy-b.yl) (b.yu-b.cy)
def Contains (b : Cell) (x y : ℝ) : Prop :=
  (b.xl:ℝ)/S ≤ x ∧ x ≤ (b.xu:ℝ)/S ∧ (b.yl:ℝ)/S ≤ y ∧ y ≤ (b.yu:ℝ)/S

theorem memX (b : Cell) {x : ℝ} (h : x ∈ Icc ((b.xl:ℝ)/S) ((b.xu:ℝ)/S)) : memAt S x b.X := by
  intro _
  exact ⟨(div_le_iff₀ S_pos).mp h.1,(le_div_iff₀ S_pos).mp h.2⟩

theorem memY (b : Cell) {y : ℝ} (h : y ∈ Icc ((b.yl:ℝ)/S) ((b.yu:ℝ)/S)) : memAt S y b.Y := by
  intro _
  exact ⟨(div_le_iff₀ S_pos).mp h.1,(le_div_iff₀ S_pos).mp h.2⟩

theorem memCst (k : ℤ) : memAt S ((k:ℝ)/S) (cst k) := by
  apply memAt_cst
  exact div_mul_cancel₀ _ S_pos.ne'

def firstCheck (e : Expr) (b : Cell) (R : ℤ) : Bool :=
  let v := e.interval (cst b.cx) (cst b.cy)
  let dx := (e.ndiff false).interval b.X b.Y
  let dy := (e.ndiff true).interval b.X b.Y
  v.ok && dx.ok && dy.ok &&
    decide (b.xl ≤ b.cx ∧ b.cx ≤ b.xu ∧ b.yl ≤ b.cy ∧ b.cy ≤ b.yu) &&
    decide (0 ≤ dx.mag ∧ 0 ≤ dy.mag) &&
    decide (S*v.mag+dx.mag*b.hx+dy.mag*b.hy ≤ R*S)

theorem firstCheck_sound (e : Expr) (b : Cell) (R : ℤ)
    (h : firstCheck e b R = true) {x y : ℝ} (hb : b.Contains x y) :
    |e.eval x y| ≤ (R:ℝ)/S := by
  simp only [firstCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hv,hdx⟩,hdy⟩,hc⟩,hn⟩,hnum⟩ := h
  let vx := (e.ndiff false).interval b.X b.Y
  let vy := (e.ndiff true).interval b.X b.Y
  let v := e.interval (cst b.cx) (cst b.cy)
  have hcx : (b.cx:ℝ)/S ∈ Icc ((b.xl:ℝ)/S) ((b.xu:ℝ)/S) := by
    constructor <;> apply div_le_div_of_nonneg_right _ S_pos.le
    · exact_mod_cast hc.1
    · exact_mod_cast hc.2.1
  have hcy : (b.cy:ℝ)/S ∈ Icc ((b.yl:ℝ)/S) ((b.yu:ℝ)/S) := by
    constructor <;> apply div_le_div_of_nonneg_right _ S_pos.le
    · exact_mod_cast hc.2.2.1
    · exact_mod_cast hc.2.2.2
  have hBx : 0 ≤ (vx.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.1) S_pos.le
  have hBy : 0 ≤ (vy.mag:ℝ)/S := div_nonneg (by exact_mod_cast hn.2) S_pos.le
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
  have hm := rectangle_mvt e.eval (e.ndiff false).eval (e.ndiff true).eval
    e.hasDerivAt_ndiff_x e.hasDerivAt_ndiff_y hcx hcy
    ⟨hb.1,hb.2.1⟩ ⟨hb.2.2.1,hb.2.2.2⟩
    (memAt_abs (e.interval_sound (memCst b.cx) (memCst b.cy)) hv)
    (fun u hu w hw => memAt_abs ((e.ndiff false).interval_sound (b.memX hu) (b.memY hw)) hdx)
    (fun u hu w hw => memAt_abs ((e.ndiff true).interval_sound (b.memX hu) (b.memY hw)) hdy)
    hBx hBy hdistx hdisty
  apply hm.trans
  have hn' : (S:ℝ)*v.mag+vx.mag*b.hx+vy.mag*b.hy ≤ (R:ℝ)*S := by exact_mod_cast hnum
  have hs : (0:ℝ) < (S:ℝ)^2 := sq_pos_of_pos S_pos
  apply (mul_le_mul_iff_left₀ hs).mp
  convert hn' using 1 <;> dsimp [v,vx,vy] <;> field_simp [S_pos.ne'] <;> ring

#check firstCheck_sound
#print axioms firstCheck_sound
end Cell
end PinnCert
