import Mathlib.Tactic.GCongr
import CellMVT
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace PinnCert
open Set

/-- A quadratic upper comparison, proved from two applications of the mean value theorem. -/
theorem taylor2_upper (f fp fpp : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt f (fp t) t)
    (hdp : ∀ t, HasDerivAt fp (fpp t) t)
    {M : ℝ} (hM : ∀ t ∈ Icc (0:ℝ) 1, |fpp t| ≤ M) :
    f 1 ≤ f 0+fp 0+M/2 := by
  let g : ℝ → ℝ := fun t => f t-f 0-fp 0*t-M*t^2/2
  have hg : ∀ t, HasDerivAt g (fp t-fp 0-M*t) t := by
    intro t
    have h := (((hd t).sub_const (f 0)).sub ((hasDerivAt_id t).const_mul (fp 0))).sub
      ((((hasDerivAt_id t).pow 2).const_mul M).div_const 2)
    convert h using 1 <;> dsimp [g] <;> ring
  have hneg : ∀ t ∈ Icc (0:ℝ) 1, fp t-fp 0-M*t ≤ 0 := by
    intro t ht
    have h := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hdp u).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hM u hu)
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) ht
    simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at h
    linarith [le_abs_self (fp t-fp 0)]
  have hc : Continuous g := (show Differentiable ℝ g from fun t => (hg t).differentiableAt).continuous
  have ha := antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1) hc.continuousOn
    (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hg t).deriv]; exact hneg t (interior_subset ht))
  have h := ha (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) zero_le_one
  dsimp [g] at h
  nlinarith

theorem taylor2_abs (f fp fpp : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt f (fp t) t)
    (hdp : ∀ t, HasDerivAt fp (fpp t) t)
    {M : ℝ} (hM : ∀ t ∈ Icc (0:ℝ) 1, |fpp t| ≤ M) :
    |f 1-f 0-fp 0| ≤ M/2 := by
  have hu := taylor2_upper f fp fpp hd hdp hM
  have hl := taylor2_upper (fun t => -f t) (fun t => -fp t) (fun t => -fpp t)
    (fun t => (hd t).neg) (fun t => (hdp t).neg)
    (fun t ht => by simpa only [abs_neg] using hM t ht)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

namespace Expr
theorem hasDerivAt_line (e : Expr) (cx cy dx dy t : ℝ) :
    HasDerivAt (fun s => e.eval (cx+s*dx) (cy+s*dy))
      ((e.diff false).eval (cx+t*dx) (cy+t*dy)*dx+
       (e.diff true).eval (cx+t*dx) (cy+t*dy)*dy) t := by
  induction e with
  | rat q => simpa [diff,eval] using hasDerivAt_const t (q:ℝ)
  | x => simpa [diff,eval] using ((hasDerivAt_id t).mul_const dx).const_add cx
  | y => simpa [diff,eval] using ((hasDerivAt_id t).mul_const dy).const_add cy
  | add a b ha hb =>
    convert ha.add hb using 1 <;> simp [eval,diff] <;> ring
  | neg a ha =>
    convert ha.neg using 1 <;> simp [eval,diff] <;> ring
  | mul a b ha hb =>
    convert ha.mul hb using 1 <;> simp [eval,diff] <;> ring
  | exp a ha =>
    convert ha.exp using 1 <;> simp [eval,diff] <;> ring
  | tanh a ha =>
    convert (hasDerivAt_tanh (a.eval (cx+t*dx) (cy+t*dy))).comp t ha using 1
    <;> simp [eval,diff,pow_two] <;> ring

theorem hasDerivAt_line_ndiff (e : Expr) (cx cy dx dy t : ℝ) :
    HasDerivAt (fun s => e.eval (cx+s*dx) (cy+s*dy))
      ((e.ndiff false).eval (cx+t*dx) (cy+t*dy)*dx+
       (e.ndiff true).eval (cx+t*dx) (cy+t*dy)*dy) t := by
  simpa [ndiff] using e.hasDerivAt_line cx cy dx dy t
end Expr

theorem segment_mem {a b c x t : ℝ} (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (ht : t ∈ Icc (0:ℝ) 1) : c+t*(x-c) ∈ Icc a b := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr ht.2),
      mul_nonneg (sub_nonneg.mpr hx.1) ht.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr ht.2),
      mul_nonneg (sub_nonneg.mpr hx.2) ht.1]

theorem four_mul_bound {a b c d u v A B C D h k : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (hu : |u| ≤ h) (hv : |v| ≤ k) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hh : 0 ≤ h) (hk : 0 ≤ k) :
    |(a*u+b*v)*u+(c*u+d*v)*v| ≤ A*h*h+B*k*h+C*h*k+D*k*k := by
  calc
    |(a*u+b*v)*u+(c*u+d*v)*v| = |a*u*u+b*v*u+c*u*v+d*v*v| := by congr 1; ring
    _ ≤ |a*u*u|+|b*v*u|+|c*u*v|+|d*v*v| := by
      have h1 := abs_add_le (a*u*u+b*v*u+c*u*v) (d*v*v)
      have h2 := abs_add_le (a*u*u+b*v*u) (c*u*v)
      have h3 := abs_add_le (a*u*u) (b*v*u)
      linarith
    _ ≤ A*h*h+B*k*h+C*h*k+D*k*k := by
      simp only [abs_mul]
      gcongr

theorem rectangle_taylor2 (e : Expr)
    {a b c d cx cy x y A Bx By Hxx Hxy Hyx Hyy hx hy : ℝ}
    (hcx : cx ∈ Icc a b) (hcy : cy ∈ Icc c d)
    (hxbox : x ∈ Icc a b) (hybox : y ∈ Icc c d)
    (hcenter : |e.eval cx cy| ≤ A)
    (hfx0 : |(e.ndiff false).eval cx cy| ≤ Bx)
    (hfy0 : |(e.ndiff true).eval cx cy| ≤ By)
    (hxx : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |((e.ndiff false).ndiff false).eval u v| ≤ Hxx)
    (hxy : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |((e.ndiff false).ndiff true).eval u v| ≤ Hxy)
    (hyx : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |((e.ndiff true).ndiff false).eval u v| ≤ Hyx)
    (hyy : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |((e.ndiff true).ndiff true).eval u v| ≤ Hyy)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hHxx : 0 ≤ Hxx) (hHxy : 0 ≤ Hxy)
    (hHyx : 0 ≤ Hyx) (hHyy : 0 ≤ Hyy)
    (hdistx : |x-cx| ≤ hx) (hdisty : |y-cy| ≤ hy) :
    |e.eval x y| ≤ A+Bx*hx+By*hy+(Hxx*hx*hx+Hxy*hy*hx+Hyx*hx*hy+Hyy*hy*hy)/2 := by
  let dx := x-cx
  let dy := y-cy
  let f := fun t => e.eval (cx+t*dx) (cy+t*dy)
  let fp := fun t => (e.ndiff false).eval (cx+t*dx) (cy+t*dy)*dx+
    (e.ndiff true).eval (cx+t*dx) (cy+t*dy)*dy
  let fpp := fun t =>
    (((e.ndiff false).ndiff false).eval (cx+t*dx) (cy+t*dy)*dx+
     ((e.ndiff false).ndiff true).eval (cx+t*dx) (cy+t*dy)*dy)*dx+
    (((e.ndiff true).ndiff false).eval (cx+t*dx) (cy+t*dy)*dx+
     ((e.ndiff true).ndiff true).eval (cx+t*dx) (cy+t*dy)*dy)*dy
  have hd : ∀ t, HasDerivAt f (fp t) t := e.hasDerivAt_line_ndiff cx cy dx dy
  have hdp : ∀ t, HasDerivAt fp (fpp t) t := fun t =>
    (((e.ndiff false).hasDerivAt_line_ndiff cx cy dx dy t).mul_const dx).add
      (((e.ndiff true).hasDerivAt_line_ndiff cx cy dx dy t).mul_const dy)
  have hhx : 0 ≤ hx := (abs_nonneg _).trans hdistx
  have hhy : 0 ≤ hy := (abs_nonneg _).trans hdisty
  have hM : ∀ t ∈ Icc (0:ℝ) 1,
      |fpp t| ≤ Hxx*hx*hx+Hxy*hy*hx+Hyx*hx*hy+Hyy*hy*hy := by
    intro t ht
    have htx := segment_mem hcx hxbox ht
    have hty := segment_mem hcy hybox ht
    exact four_mul_bound (hxx _ htx _ hty) (hxy _ htx _ hty)
      (hyx _ htx _ hty) (hyy _ htx _ hty) hdistx hdisty hHxx hHxy hHyx hHyy hhx hhy
  have h := taylor2_abs f fp fpp hd hdp hM
  dsimp [f,fp,dx,dy] at h
  simp only [one_mul,zero_mul,add_zero,add_sub_cancel] at h
  have hfp : |(e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy)| ≤ Bx*hx+By*hy := by
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    gcongr
  have htri := abs_add_le
    (e.eval x y-e.eval cx cy-((e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy)))
    (e.eval cx cy+((e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy)))
  have hcan : e.eval x y-e.eval cx cy-
      ((e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy))+
      (e.eval cx cy+((e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy))) = e.eval x y := by ring
  rw [hcan] at htri
  have htri2 := abs_add_le (e.eval cx cy)
    ((e.ndiff false).eval cx cy*(x-cx)+(e.ndiff true).eval cx cy*(y-cy))
  linarith

#check taylor2_abs
#print axioms taylor2_abs
#print axioms Expr.hasDerivAt_line_ndiff
#print axioms rectangle_taylor2
end PinnCert
