import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! A classical square maximum principle. This is analytic infrastructure;
no neural interval or numerical certificate is asserted here. The first
version deliberately states global coordinate twice-differentiability. -/
namespace PoissonR3
open Set Filter Topology
noncomputable section

def Q : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
def Edge (z : ℝ × ℝ) : Prop := z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1
def Lap (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv (fun t => F t y)) x + deriv (deriv (fun t => F x t)) y

def Twice (f : ℝ → ℝ) : Prop := Differentiable ℝ f ∧ Differentiable ℝ (deriv f)
def CoordTwo (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ y, Twice (fun x => F x y)) ∧ (∀ x, Twice (fun y => F x y))

lemma localMax_second_nonpos {f : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMax f a) (hc : ContinuousAt f a) : deriv (deriv f) a ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) a := lt_of_not_ge hn
  have hmin : IsLocalMin f a := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [h, hmin] with x hx hy
    exact le_antisymm hx hy
  have hd := heq.deriv.deriv_eq
  simp only [deriv_const'] at hd
  linarith

lemma square_strict_maximum (F : ℝ → ℝ → ℝ) (k : ℝ)
    (hc : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) Q)
    (hd : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      ContinuousAt (fun t => F t y) x ∧ ContinuousAt (fun t => F x t) y)
    (hl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → 0 < Lap F x y)
    (hb : ∀ z ∈ Q, Edge z → F z.1 z.2 ≤ k) :
    ∀ z ∈ Q, F z.1 z.2 ≤ k := by
  have hcompact : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hne : Q.Nonempty := ⟨(0,0), by norm_num [Q]⟩
  obtain ⟨a, ha, hm⟩ := hcompact.exists_isMaxOn hne hc
  have hbound : F a.1 a.2 ≤ k := by
    by_cases he : Edge a
    · exact hb a ha he
    · have hx : a.1 ∈ Ioo (0:ℝ) 1 := by
        have hq := ha.1
        have h0 : a.1 ≠ 0 := fun h => he (Or.inl h)
        have h1 : a.1 ≠ 1 := fun h => he (Or.inr (Or.inl h))
        exact ⟨lt_of_le_of_ne hq.1 (Ne.symm h0), lt_of_le_of_ne hq.2 h1⟩
      have hy : a.2 ∈ Ioo (0:ℝ) 1 := by
        have hq := ha.2
        have h0 : a.2 ≠ 0 := fun h => he (Or.inr (Or.inr (Or.inl h)))
        have h1 : a.2 ≠ 1 := fun h => he (Or.inr (Or.inr (Or.inr h)))
        exact ⟨lt_of_le_of_ne hq.1 (Ne.symm h0), lt_of_le_of_ne hq.2 h1⟩
      have hmx : IsMaxOn (fun t => F t a.2) (Icc (0:ℝ) 1) a.1 := by
        intro t ht
        exact hm (show (t,a.2) ∈ Q from ⟨ht,ha.2⟩)
      have hmy : IsMaxOn (fun t => F a.1 t) (Icc (0:ℝ) 1) a.2 := by
        intro t ht
        exact hm (show (a.1,t) ∈ Q from ⟨ha.1,ht⟩)
      have hxx := localMax_second_nonpos (hmx.isLocalMax (Icc_mem_nhds hx.1 hx.2)) (hd _ _ hx hy).1
      have hyy := localMax_second_nonpos (hmy.isLocalMax (Icc_mem_nhds hy.1 hy.2)) (hd _ _ hx hy).2
      have hp := hl _ _ hx hy
      dsimp [Lap] at hp
      linarith
  intro z hz
  exact (hm hz).trans hbound

lemma deriv2_add {f g : ℝ → ℝ} (hf : Twice f) (hg : Twice g) (x : ℝ) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have he : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t := by
    funext t
    exact deriv_add (hf.1 t) (hg.1 t)
  rw [he]
  exact deriv_add (hf.2 x) (hg.2 x)

lemma twice_add {f g : ℝ → ℝ} (hf : Twice f) (hg : Twice g) :
    Twice (fun t => f t + g t) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have he : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t := by
    funext t
    exact deriv_add (hf.1 t) (hg.1 t)
  rw [he]
  exact hf.2.add hg.2

lemma quad_twice (eps c : ℝ) : Twice (fun t : ℝ => eps * (t^2+c)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => eps * (t^2+c)) (eps*(2*t)) t := by
    convert (((hasDerivAt_id t).pow 2).add_const c).const_mul eps using 1 <;> simp
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (fun t : ℝ => eps*(t^2+c)) = fun t => eps*(2*t) := funext fun t => (hd t).deriv
  rw [he]
  fun_prop

lemma quad_deriv2 (eps c x : ℝ) : deriv (deriv (fun t : ℝ => eps*(t^2+c))) x = 2*eps := by
  have he : deriv (fun t : ℝ => eps*(t^2+c)) = fun t => eps*(2*t) := by
    funext t
    convert ((((hasDerivAt_id t).pow 2).add_const c).const_mul eps).deriv using 1 <;> simp
  rw [he]
  convert (((hasDerivAt_id x).const_mul 2).const_mul eps).deriv using 1 <;> ring

lemma square_maximum (F : ℝ → ℝ → ℝ)
    (hc : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) Q)
    (hd : CoordTwo F)
    (hl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → 0 ≤ Lap F x y)
    (hb : ∀ z ∈ Q, Edge z → F z.1 z.2 ≤ 0) :
    ∀ z ∈ Q, F z.1 z.2 ≤ 0 := by
  intro z hz
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let eps := delta/2
  have heps : 0 < eps := half_pos hdelta
  let G : ℝ → ℝ → ℝ := fun x y => F x y + eps*(x^2+y^2)
  have hGc : ContinuousOn (fun z : ℝ × ℝ => G z.1 z.2) Q := by
    exact hc.add (by fun_prop)
  have hGd : CoordTwo G := by
    constructor
    · intro y
      exact twice_add (hd.1 y) (quad_twice eps (y^2))
    · intro x
      have he : (fun y => eps*(x^2+y^2)) = fun y => eps*(y^2+x^2) := by funext y; ring
      dsimp [G]
      exact twice_add (hd.2 x) (he ▸ quad_twice eps (x^2))
  have hGl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → 0 < Lap G x y := by
    intro x y hx hy
    have he : (fun t : ℝ => eps*(x^2+t^2)) = fun t => eps*(t^2+x^2) := by funext t; ring
    dsimp [Lap, G]
    rw [deriv2_add (hd.1 y) (quad_twice eps (y^2)) x]
    have hqy : Twice (fun t : ℝ => eps*(x^2+t^2)) := he ▸ quad_twice eps (x^2)
    rw [deriv2_add (hd.2 x) hqy y, he, quad_deriv2, quad_deriv2]
    have hh := hl x y hx hy
    dsimp [Lap] at hh
    linarith
  have hGb : ∀ a ∈ Q, Edge a → G a.1 a.2 ≤ 2*eps := by
    intro a ha he
    have h := hb a ha he
    have hx : a.1^2 ≤ 1 := by nlinarith [ha.1.1,ha.1.2]
    have hy : a.2^2 ≤ 1 := by nlinarith [ha.2.1,ha.2.2]
    have hm := mul_le_mul_of_nonneg_left (show a.1^2+a.2^2 ≤ 2 by linarith) heps.le
    dsimp [G]
    linarith
  have hG := square_strict_maximum G (2*eps) hGc
    (fun x y _ _ => ⟨(hGd.1 y).1.continuous.continuousAt, (hGd.2 x).1.continuous.continuousAt⟩) hGl hGb z hz
  have hp := mul_nonneg heps.le (add_nonneg (sq_nonneg z.1) (sq_nonneg z.2))
  dsimp [G, eps] at hG hp
  linarith


/-- Local hypotheses suffice: differentiable on a neighborhood, derivative differentiable at x. -/
def TwiceAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t) ∧ DifferentiableAt ℝ (deriv f) x

def CoordTwoOn (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
    TwiceAt (fun t => F t y) x ∧ TwiceAt (fun t => F x t) y

lemma Twice.at {f : ℝ → ℝ} (h : Twice f) (x : ℝ) : TwiceAt f x :=
  ⟨Filter.Eventually.of_forall h.1, h.2 x⟩

lemma TwiceAt.continuousAt {f : ℝ → ℝ} {x : ℝ} (h : TwiceAt f x) : ContinuousAt f x :=
  h.1.self_of_nhds.continuousAt

lemma deriv2_add_at {f g : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (hg : TwiceAt g x) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have he : deriv (fun t => f t + g t) =ᶠ[𝓝 x] (fun t => deriv f t + deriv g t) := by
    filter_upwards [hf.1,hg.1] with t ht hu
    exact deriv_add ht hu
  rw [he.deriv_eq]
  exact deriv_add hf.2 hg.2

lemma twiceAt_add {f g : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (hg : TwiceAt g x) :
    TwiceAt (fun t => f t + g t) x := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1,hg.1] with t ht hu
    exact ht.add hu
  · have he : deriv (fun t => f t + g t) =ᶠ[𝓝 x] (fun t => deriv f t + deriv g t) := by
      filter_upwards [hf.1,hg.1] with t ht hu
      exact deriv_add ht hu
    exact (hf.2.add hg.2).congr_of_eventuallyEq he

lemma square_maximum_local (F : ℝ → ℝ → ℝ)
    (hc : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) Q)
    (hd : CoordTwoOn F)
    (hl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → 0 ≤ Lap F x y)
    (hb : ∀ z ∈ Q, Edge z → F z.1 z.2 ≤ 0) :
    ∀ z ∈ Q, F z.1 z.2 ≤ 0 := by
  intro z hz
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let eps := delta/2
  have heps : 0 < eps := half_pos hdelta
  let G : ℝ → ℝ → ℝ := fun x y => F x y + eps*(x^2+y^2)
  have hGc : ContinuousOn (fun z : ℝ × ℝ => G z.1 z.2) Q := by
    exact hc.add (by fun_prop)
  have hGd : CoordTwoOn G := by
    intro x y hx hy
    have h := hd x y hx hy
    constructor
    · exact twiceAt_add h.1 ((quad_twice eps (y^2)).at x)
    · have he : (fun y => eps*(x^2+y^2)) = fun y => eps*(y^2+x^2) := by funext y; ring
      dsimp [G]
      exact twiceAt_add h.2 (he ▸ (quad_twice eps (x^2)).at y)
  have hGl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → 0 < Lap G x y := by
    intro x y hx hy
    have h := hd x y hx hy
    have he : (fun t : ℝ => eps*(x^2+t^2)) = fun t => eps*(t^2+x^2) := by funext t; ring
    dsimp [Lap, G]
    rw [deriv2_add_at h.1 ((quad_twice eps (y^2)).at x)]
    have hqy : TwiceAt (fun t : ℝ => eps*(x^2+t^2)) y := he ▸ (quad_twice eps (x^2)).at y
    rw [deriv2_add_at h.2 hqy, he, quad_deriv2, quad_deriv2]
    have hh := hl x y hx hy
    dsimp [Lap] at hh
    linarith
  have hGb : ∀ a ∈ Q, Edge a → G a.1 a.2 ≤ 2*eps := by
    intro a ha he
    have h := hb a ha he
    have hx : a.1^2 ≤ 1 := by nlinarith [ha.1.1,ha.1.2]
    have hy : a.2^2 ≤ 1 := by nlinarith [ha.2.1,ha.2.2]
    have hm := mul_le_mul_of_nonneg_left (show a.1^2+a.2^2 ≤ 2 by linarith) heps.le
    dsimp [G]
    linarith
  have hG := square_strict_maximum G (2*eps) hGc
    (fun x y hx hy => ⟨(hGd x y hx hy).1.continuousAt, (hGd x y hx hy).2.continuousAt⟩) hGl hGb z hz
  have hp := mul_nonneg heps.le (add_nonneg (sq_nonneg z.1) (sq_nonneg z.2))
  dsimp [G, eps] at hG hp
  linarith

#check square_maximum_local
#print axioms square_maximum_local

#check localMax_second_nonpos
#check square_strict_maximum
#check square_maximum
#print axioms localMax_second_nonpos
#print axioms square_strict_maximum
#print axioms square_maximum
end
end PoissonR3
