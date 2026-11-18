import Transfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace PoissonR3
open Set Filter Topology PoissonPilot
noncomputable section

@[fun_prop] lemma smooth_tanh : ContDiff ℝ 2 Real.tanh := by
  have he : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

def T : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t
  | n+2, t => 2*t*T (n+1) t-T n t

@[fun_prop] lemma smooth_T (n : ℕ) : ContDiff ℝ 2 (T n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [T]; fun_prop
  | one => simp only [T]; fun_prop
  | more n h0 h1 => simp only [T]; fun_prop

-- Exact checkpoint SHA256 d124e3a08471dcb0dd98d74ba2483deda368934024c00fa34f8f3a7e53d94dcb
def N (x y : ℝ) : ℝ := p x*p y*(
  ((33653889:ℝ)/16777216) +
  ((-12498155:ℝ)/16777216) * Real.tanh (((10028835:ℝ)/16777216)*x+((-15697194:ℝ)/16777216)*y+((-6582840:ℝ)/16777216)) +
  ((12311660:ℝ)/16777216) * Real.tanh (((-3130818:ℝ)/16777216)*x+((21325544:ℝ)/16777216)*y+((-9770752:ℝ)/16777216)) +
  ((-17419905:ℝ)/16777216) * Real.tanh (((2687543:ℝ)/16777216)*x+((16410348:ℝ)/16777216)*y+((-36535174:ℝ)/16777216)) +
  ((-18087057:ℝ)/16777216) * Real.tanh (((-663358:ℝ)/16777216)*x+((-24569170:ℝ)/16777216)*y+((27618223:ℝ)/16777216)) +
  ((-3965151:ℝ)/16777216) * Real.tanh (((-4041981:ℝ)/16777216)*x+((-3009566:ℝ)/16777216)*y+((2549353:ℝ)/16777216)) +
  ((29531713:ℝ)/16777216) * Real.tanh (((8636176:ℝ)/16777216)*x+((-15380473:ℝ)/16777216)*y+((18162178:ℝ)/16777216)) +
  ((16099143:ℝ)/16777216) * Real.tanh (((-5106673:ℝ)/16777216)*x+((3928507:ℝ)/16777216)*y+((15874471:ℝ)/16777216)) +
  ((11711319:ℝ)/16777216) * Real.tanh (((7559742:ℝ)/16777216)*x+((-3179262:ℝ)/16777216)*y+((18205620:ℝ)/16777216)) +
  ((-36544829:ℝ)/16777216) * Real.tanh (((-19705717:ℝ)/16777216)*x+((-26808326:ℝ)/16777216)*y+((62892144:ℝ)/16777216)) +
  ((25901550:ℝ)/16777216) * Real.tanh (((8815791:ℝ)/16777216)*x+((-9856854:ℝ)/16777216)*y+((3435363:ℝ)/16777216)) +
  ((-10758100:ℝ)/16777216) * Real.tanh (((-12082314:ℝ)/16777216)*x+((11617157:ℝ)/16777216)*y+((4421606:ℝ)/16777216)) +
  ((7035087:ℝ)/16777216) * Real.tanh (((-6705311:ℝ)/16777216)*x+((10513409:ℝ)/16777216)*y+((9029355:ℝ)/16777216)) +
  ((-2900717:ℝ)/16777216) * Real.tanh (((-2324014:ℝ)/16777216)*x+((-3725155:ℝ)/16777216)*y+((-4407648:ℝ)/16777216)) +
  ((18808434:ℝ)/16777216) * Real.tanh (((-14904796:ℝ)/16777216)*x+((-304757:ℝ)/16777216)*y+((-4749268:ℝ)/16777216)) +
  ((-27769719:ℝ)/16777216) * Real.tanh (((-14440123:ℝ)/16777216)*x+((-19046938:ℝ)/16777216)*y+((49964766:ℝ)/16777216)) +
  ((6561356:ℝ)/16777216) * Real.tanh (((-4170089:ℝ)/16777216)*x+((6779566:ℝ)/16777216)*y+((9261507:ℝ)/16777216)))

-- Exact correction SHA256 22f79f0c37d40cae3668e0147bd6bfece0a71d632c727760294238302e1afae1
def C (x y : ℝ) : ℝ := p x*p y*(
  ((-114867262:ℝ)/1099511627776) * T 0 (2*x-1) * T 0 (2*y-1) +
  ((62159804:ℝ)/1099511627776) * T 0 (2*x-1) * T 1 (2*y-1) +
  ((-168867553:ℝ)/1099511627776) * T 0 (2*x-1) * T 2 (2*y-1) +
  ((41678863:ℝ)/1099511627776) * T 0 (2*x-1) * T 3 (2*y-1) +
  ((-86185053:ℝ)/1099511627776) * T 0 (2*x-1) * T 4 (2*y-1) +
  ((-20277005:ℝ)/1099511627776) * T 0 (2*x-1) * T 5 (2*y-1) +
  ((-27389138:ℝ)/1099511627776) * T 0 (2*x-1) * T 6 (2*y-1) +
  ((-476900472:ℝ)/1099511627776) * T 1 (2*x-1) * T 0 (2*y-1) +
  ((-997341545:ℝ)/1099511627776) * T 1 (2*x-1) * T 1 (2*y-1) +
  ((-405836774:ℝ)/1099511627776) * T 1 (2*x-1) * T 2 (2*y-1) +
  ((-662624015:ℝ)/1099511627776) * T 1 (2*x-1) * T 3 (2*y-1) +
  ((-88354583:ℝ)/1099511627776) * T 1 (2*x-1) * T 4 (2*y-1) +
  ((23204417:ℝ)/1099511627776) * T 1 (2*x-1) * T 5 (2*y-1) +
  ((14878903:ℝ)/1099511627776) * T 1 (2*x-1) * T 6 (2*y-1) +
  ((-202954182:ℝ)/1099511627776) * T 2 (2*x-1) * T 0 (2*y-1) +
  ((117567576:ℝ)/1099511627776) * T 2 (2*x-1) * T 1 (2*y-1) +
  ((-315753791:ℝ)/1099511627776) * T 2 (2*x-1) * T 2 (2*y-1) +
  ((57021435:ℝ)/1099511627776) * T 2 (2*x-1) * T 3 (2*y-1) +
  ((-120417951:ℝ)/1099511627776) * T 2 (2*x-1) * T 4 (2*y-1) +
  ((-67310150:ℝ)/1099511627776) * T 2 (2*x-1) * T 5 (2*y-1) +
  ((-23760326:ℝ)/1099511627776) * T 2 (2*x-1) * T 6 (2*y-1) +
  ((-259431907:ℝ)/1099511627776) * T 3 (2*x-1) * T 0 (2*y-1) +
  ((-477532559:ℝ)/1099511627776) * T 3 (2*x-1) * T 1 (2*y-1) +
  ((-263697813:ℝ)/1099511627776) * T 3 (2*x-1) * T 2 (2*y-1) +
  ((-352309607:ℝ)/1099511627776) * T 3 (2*x-1) * T 3 (2*y-1) +
  ((-127897494:ℝ)/1099511627776) * T 3 (2*x-1) * T 4 (2*y-1) +
  ((-25468296:ℝ)/1099511627776) * T 3 (2*x-1) * T 5 (2*y-1) +
  ((-4886241:ℝ)/1099511627776) * T 3 (2*x-1) * T 6 (2*y-1) +
  ((-93900003:ℝ)/1099511627776) * T 4 (2*x-1) * T 0 (2*y-1) +
  ((27202392:ℝ)/1099511627776) * T 4 (2*x-1) * T 1 (2*y-1) +
  ((-122713092:ℝ)/1099511627776) * T 4 (2*x-1) * T 2 (2*y-1) +
  ((-80569815:ℝ)/1099511627776) * T 4 (2*x-1) * T 3 (2*y-1) +
  ((-38562128:ℝ)/1099511627776) * T 4 (2*x-1) * T 4 (2*y-1) +
  ((-8248970:ℝ)/1099511627776) * T 4 (2*x-1) * T 5 (2*y-1) +
  ((-874640:ℝ)/1099511627776) * T 4 (2*x-1) * T 6 (2*y-1) +
  ((107049604:ℝ)/1099511627776) * T 5 (2*x-1) * T 0 (2*y-1) +
  ((-24072645:ℝ)/1099511627776) * T 5 (2*x-1) * T 1 (2*y-1) +
  ((-43611416:ℝ)/1099511627776) * T 5 (2*x-1) * T 2 (2*y-1) +
  ((-15515650:ℝ)/1099511627776) * T 5 (2*x-1) * T 3 (2*y-1) +
  ((-4615678:ℝ)/1099511627776) * T 5 (2*x-1) * T 4 (2*y-1) +
  ((-938550:ℝ)/1099511627776) * T 5 (2*x-1) * T 5 (2*y-1) +
  ((20939:ℝ)/1099511627776) * T 5 (2*x-1) * T 6 (2*y-1) +
  ((-1715638:ℝ)/1099511627776) * T 6 (2*x-1) * T 0 (2*y-1) +
  ((-7051765:ℝ)/1099511627776) * T 6 (2*x-1) * T 1 (2*y-1) +
  ((-7873644:ℝ)/1099511627776) * T 6 (2*x-1) * T 2 (2*y-1) +
  ((-2673671:ℝ)/1099511627776) * T 6 (2*x-1) * T 3 (2*y-1) +
  ((-455592:ℝ)/1099511627776) * T 6 (2*x-1) * T 4 (2*y-1) +
  ((205163:ℝ)/1099511627776) * T 6 (2*x-1) * T 5 (2*y-1) +
  ((10147:ℝ)/1099511627776) * T 6 (2*x-1) * T 6 (2*y-1))

def U (x y : ℝ) : ℝ := p x*p y*Real.exp (x*y)
def forcing (x y : ℝ) : ℝ := Real.exp (x*y) *
  (2*(p x+p y)-2*(y*p y*dp x+x*p x*dp y)-p x*p y*(x^2+y^2))

@[fun_prop] theorem N_smooth : ContDiff ℝ 2 (fun z : ℝ × ℝ => N z.1 z.2) := by
  unfold N p
  fun_prop
@[fun_prop] theorem C_smooth : ContDiff ℝ 2 (fun z : ℝ × ℝ => C z.1 z.2) := by
  unfold C p
  fun_prop
@[fun_prop] theorem U_smooth : ContDiff ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) := by
  unfold U p
  fun_prop

lemma coord_of_smooth (F : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2)) : CoordTwoOn F := by
  intro x y _ _
  have hx : ContDiff ℝ 2 (fun t => F t y) := h.comp (contDiff_id.prodMk contDiff_const)
  have hy : ContDiff ℝ 2 (fun t => F x t) := h.comp (contDiff_const.prodMk contDiff_id)
  exact ⟨(show Twice (fun t => F t y) from ⟨hx.differentiable (by norm_num),hx.differentiable_deriv_two⟩).at x,
    (show Twice (fun t => F x t) from ⟨hy.differentiable (by norm_num),hy.differentiable_deriv_two⟩).at y⟩

lemma N_boundary (z : ℝ × ℝ) (h : Edge z) : N z.1 z.2 = 0 := by
  rcases h with h|h|h|h <;> simp [N,p,h]
lemma C_boundary (z : ℝ × ℝ) (h : Edge z) : C z.1 z.2 = 0 := by
  rcases h with h|h|h|h <;> simp [C,p,h]
lemma U_boundary (z : ℝ × ℝ) (h : Edge z) : U z.1 z.2 = 0 := by
  rcases h with h|h|h|h <;> simp [U,p,h]

def Ux (x y : ℝ) : ℝ := p y*Real.exp (x*y)*(dp x+p x*y)
def Uxx (x y : ℝ) : ℝ := p y*Real.exp (x*y)*(-2+2*dp x*y+p x*y^2)
lemma U_deriv (x y : ℝ) : HasDerivAt (fun t => U t y) (Ux x y) x := by
  have hE := ((hasDerivAt_id x).mul_const y).exp
  have h := ((hasDerivAt_p x).mul_const (p y)).mul hE
  convert h using 1 <;> dsimp [U,Ux] <;> ring
lemma Ux_deriv (x y : ℝ) : HasDerivAt (fun t => Ux t y) (Uxx x y) x := by
  have hE := ((hasDerivAt_id x).mul_const y).exp
  have h := (hE.const_mul (p y)).mul ((hasDerivAt_dp x).add ((hasDerivAt_p x).mul_const y))
  convert h using 1 <;> dsimp [Ux,Uxx] <;> ring
lemma U_deriv2 (x y : ℝ) : deriv (deriv (fun t => U t y)) x = Uxx x y := by
  have h : deriv (fun t => U t y) = fun t => Ux t y := funext fun t => (U_deriv t y).deriv
  rw [h]
  exact (Ux_deriv x y).deriv
lemma U_symm (x y : ℝ) : U x y = U y x := by
  simp [U,mul_comm,mul_left_comm,mul_assoc]

theorem manufactured_pde (x y : ℝ) : -Lap U x y = forcing x y := by
  have h : (fun t => U x t) = fun t => U t x := funext fun t => U_symm x t
  dsimp [Lap]
  rw [h,U_deriv2,U_deriv2]
  dsimp [Uxx,forcing,p,dp]
  rw [mul_comm y x]
  ring

theorem poisson_unique (u v f : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q)
    (hcv : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) Q)
    (hdu : CoordTwoOn u) (hdv : CoordTwoOn v)
    (hb : ∀ z ∈ Q, Edge z → u z.1 z.2 = v z.1 z.2)
    (hu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=f x y)
    (hv : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap v x y=f x y) :
    ∀ z ∈ Q, u z.1 z.2=v z.1 z.2 := by
  have h := residual_error (fun x y => u x y-v x y) 0 (by norm_num) (hcu.sub hcv) (hdu.sub hdv)
    (fun z hz he => sub_eq_zero.mpr (hb z hz he))
    (fun x y hx hy => by
      rw [lap_sub hdu hdv hx hy]
      have h1 := hu x y hx hy
      have h2 := hv x y hx hy
      have he : Lap u x y-Lap v x y=0 := by linarith
      rw [he]; simp)
  intro z hz
  have hh := h z hz
  have hle : |u z.1 z.2-v z.1 z.2| ≤ 0 := by simpa using hh
  have hz0 : |u z.1 z.2-v z.1 z.2| = 0 := le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz0)

#check N_smooth
#check C_smooth
#check manufactured_pde
#check poisson_unique
#print axioms N_smooth
#print axioms C_smooth
#print axioms manufactured_pde
#print axioms poisson_unique
end
end PoissonR3
