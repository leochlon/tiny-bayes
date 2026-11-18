import Maximum
import BarrierComponents

/-! Actual classical residual-to-error transfer. Its residual and correction
norm hypotheses are explicit. No computed neural bounds are discharged. -/
namespace PoissonR3
open Set Filter Topology PoissonPilot
noncomputable section

lemma deriv2_sub_at {f g : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (hg : TwiceAt g x) :
    deriv (deriv (fun t => f t - g t)) x = deriv (deriv f) x - deriv (deriv g) x := by
  have he : deriv (fun t => f t - g t) =ᶠ[𝓝 x] (fun t => deriv f t - deriv g t) := by
    filter_upwards [hf.1,hg.1] with t ht hu
    exact deriv_sub ht hu
  rw [he.deriv_eq]
  exact deriv_sub hf.2 hg.2

lemma twiceAt_sub {f g : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (hg : TwiceAt g x) :
    TwiceAt (fun t => f t - g t) x := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1,hg.1] with t ht hu
    exact ht.sub hu
  · have he : deriv (fun t => f t - g t) =ᶠ[𝓝 x] (fun t => deriv f t - deriv g t) := by
      filter_upwards [hf.1,hg.1] with t ht hu
      exact deriv_sub ht hu
    exact (hf.2.sub hg.2).congr_of_eventuallyEq he

lemma deriv2_scale_at {f : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (a : ℝ) :
    deriv (deriv (fun t => a*f t)) x = a*deriv (deriv f) x := by
  have he : deriv (fun t => a*f t) =ᶠ[𝓝 x] (fun t => a*deriv f t) := by
    filter_upwards [hf.1] with t ht
    exact (ht.hasDerivAt.const_mul a).deriv
  rw [he.deriv_eq]
  exact (hf.2.hasDerivAt.const_mul a).deriv

lemma twiceAt_scale {f : ℝ → ℝ} {x : ℝ} (hf : TwiceAt f x) (a : ℝ) :
    TwiceAt (fun t => a*f t) x := by
  refine ⟨hf.1.mono (fun t ht => ht.const_mul a), ?_⟩
  have he : deriv (fun t => a*f t) =ᶠ[𝓝 x] (fun t => a*deriv f t) := by
    filter_upwards [hf.1] with t ht
    exact (ht.hasDerivAt.const_mul a).deriv
  exact (hf.2.const_mul a).congr_of_eventuallyEq he

lemma CoordTwoOn.sub {F G : ℝ → ℝ → ℝ} (hf : CoordTwoOn F) (hg : CoordTwoOn G) :
    CoordTwoOn (fun x y => F x y - G x y) := by
  intro x y hx hy
  exact ⟨twiceAt_sub (hf x y hx hy).1 (hg x y hx hy).1,
    twiceAt_sub (hf x y hx hy).2 (hg x y hx hy).2⟩

lemma CoordTwoOn.scale {F : ℝ → ℝ → ℝ} (hf : CoordTwoOn F) (a : ℝ) :
    CoordTwoOn (fun x y => a*F x y) := by
  intro x y hx hy
  exact ⟨twiceAt_scale (hf x y hx hy).1 a, twiceAt_scale (hf x y hx hy).2 a⟩

lemma lap_sub {F G : ℝ → ℝ → ℝ} (hf : CoordTwoOn F) (hg : CoordTwoOn G)
    {x y : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) (hy : y ∈ Ioo (0:ℝ) 1) :
    Lap (fun x y => F x y - G x y) x y = Lap F x y - Lap G x y := by
  dsimp [Lap]
  rw [deriv2_sub_at (hf x y hx hy).1 (hg x y hx hy).1,
    deriv2_sub_at (hf x y hx hy).2 (hg x y hx hy).2]
  ring

lemma lap_scale {F : ℝ → ℝ → ℝ} (hf : CoordTwoOn F) (a : ℝ)
    {x y : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) (hy : y ∈ Ioo (0:ℝ) 1) :
    Lap (fun x y => a*F x y) x y = a*Lap F x y := by
  dsimp [Lap]
  rw [deriv2_scale_at (hf x y hx hy).1 a, deriv2_scale_at (hf x y hx hy).2 a]
  ring

lemma barrier_deriv2 (x y : ℝ) : deriv (deriv (fun t => B t y)) x = Bxx x y := by
  have he : deriv (fun t => B t y) = fun t => Bx t y := funext fun t => (hasDerivAt_B t y).deriv
  rw [he]
  exact (hasDerivAt_Bx x y).deriv

lemma barrier_lap (x y : ℝ) : Lap B x y = -1 := by
  have he : (fun t => B x t) = fun t => B t x := funext fun t => B_symm x t
  dsimp [Lap]
  rw [he,barrier_deriv2,barrier_deriv2]
  have h := negative_laplacian x y
  linarith

lemma barrier_coord : CoordTwoOn B := by
  have htw (y : ℝ) : Twice (fun t => B t y) := by
    refine ⟨fun t => (hasDerivAt_B t y).differentiableAt, ?_⟩
    have he : deriv (fun t => B t y) = fun t => Bx t y := funext fun t => (hasDerivAt_B t y).deriv
    rw [he]
    exact fun t => (hasDerivAt_Bx t y).differentiableAt
  intro x y _ _
  have he : (fun t => B x t) = fun t => B t x := funext fun t => B_symm x t
  exact ⟨(htw y).at x, he ▸ (htw x).at y⟩

lemma barrier_cont : Continuous (fun z : ℝ × ℝ => B z.1 z.2) := by
  dsimp [B,p]
  fun_prop

lemma upper_comparison (e : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ContinuousOn (fun z : ℝ × ℝ => e z.1 z.2) Q) (hd : CoordTwoOn e)
    (hb : ∀ z ∈ Q, Edge z → e z.1 z.2 ≤ 0)
    (hl : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -R ≤ Lap e x y) :
    ∀ z ∈ Q, e z.1 z.2 ≤ R*B z.1 z.2 := by
  have hh := square_maximum_local (fun x y => e x y - R*B x y)
    (hc.sub (continuous_const.mul barrier_cont).continuousOn) (hd.sub (barrier_coord.scale R))
  have hll : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      0 ≤ Lap (fun x y => e x y - R*B x y) x y := by
    intro x y hx hy
    rw [lap_sub hd (barrier_coord.scale R) hx hy, lap_scale barrier_coord R hx hy,barrier_lap]
    have h := hl x y hx hy
    linarith
  have hbb : ∀ z ∈ Q, Edge z → e z.1 z.2 - R*B z.1 z.2 ≤ 0 := by
    intro z hz he
    have h0 := hb z hz he
    have h1 := mul_nonneg hR (barrier_nonneg hz.1.1 hz.1.2 hz.2.1 hz.2.2)
    linarith
  intro z hz
  have h := hh hll hbb z hz
  linarith

/-- Uniform error follows from an ACTUAL Laplacian bound and zero boundary. -/
theorem residual_error (e : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ContinuousOn (fun z : ℝ × ℝ => e z.1 z.2) Q) (hd : CoordTwoOn e)
    (hb : ∀ z ∈ Q, Edge z → e z.1 z.2 = 0)
    (hr : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → |Lap e x y| ≤ R) :
    ∀ z ∈ Q, |e z.1 z.2| ≤ 3*R/40 := by
  have hu := upper_comparison e R hR hc hd (fun z hz he => (hb z hz he).le)
    (fun x y hx hy => (abs_le.mp (hr x y hx hy)).1)
  have hdneg := hd.scale (-1)
  have hl := upper_comparison (fun x y => (-1)*e x y) R hR
    ((continuousOn_const.mul hc)) hdneg
    (fun z hz he => by dsimp; rw [hb z hz he]; simp)
    (fun x y hx hy => by
      rw [lap_scale hd (-1) hx hy]
      have h := (abs_le.mp (hr x y hx hy)).2
      linarith)
  intro z hz
  exact comparison_conclusion hz.1.1 hz.1.2 hz.2.1 hz.2.2 hR (hu z hz) (by simpa using hl z hz)

/-- The auxiliary correction preserves a bound on the ORIGINAL network error. -/
theorem corrected_poisson (N u C f : ℝ → ℝ → ℝ) (A R : ℝ) (hR : 0 ≤ R)
    (hcN : ContinuousOn (fun z : ℝ × ℝ => N z.1 z.2) Q)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q)
    (hcC : ContinuousOn (fun z : ℝ × ℝ => C z.1 z.2) Q)
    (hdN : CoordTwoOn N) (hdu : CoordTwoOn u) (hdC : CoordTwoOn C)
    (hb : ∀ z ∈ Q, Edge z → N z.1 z.2 = 0 ∧ u z.1 z.2 = 0 ∧ C z.1 z.2 = 0)
    (hu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y = f x y)
    (hC : ∀ z ∈ Q, |C z.1 z.2| ≤ A)
    (hres : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      |(-Lap (fun x y => N x y-C x y) x y)-f x y| ≤ R) :
    ∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ A+3*R/40 := by
  let E := fun x y => (N x y-C x y)-u x y
  have he := residual_error E R hR ((hcN.sub hcC).sub hcu) ((hdN.sub hdC).sub hdu)
  have heB : ∀ z ∈ Q, Edge z → E z.1 z.2 = 0 := by
    intro z hz he
    have h := hb z hz he
    dsimp [E]
    rw [h.1,h.2.1,h.2.2]
    ring
  have heR : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → |Lap E x y| ≤ R := by
    intro x y hx hy
    have h := hres x y hx hy
    have hh := hu x y hx hy
    dsimp [E]
    rw [lap_sub (hdN.sub hdC) hdu hx hy]
    have heq : (-Lap (fun x y => N x y-C x y) x y)-f x y =
        -(Lap (fun x y => N x y-C x y) x y-Lap u x y) := by linarith
    rw [heq,abs_neg] at h
    exact h
  intro z hz
  have hez := he heB heR z hz
  have hcz := hC z hz
  have heparts := abs_le.mp hez
  have hcparts := abs_le.mp hcz
  dsimp [E] at heparts
  rw [abs_le]
  constructor <;> linarith

#check barrier_lap
#check residual_error
#check corrected_poisson
#print axioms barrier_lap
#print axioms residual_error
#print axioms corrected_poisson
end
end PoissonR3
