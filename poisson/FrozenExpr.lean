import ExprInterval
import Candidate

namespace PinnCert
open Expr

def bubble (a : Expr) : Expr := a*(1-a)
def dbubble (a : Expr) : Expr := 1-2*a

def cheb : ℕ → Expr → Expr
  | 0, _ => 1
  | 1, a => a
  | n+2, a => 2*a*cheb (n+1) a-cheb n a

theorem eval_cheb (n : ℕ) (a : Expr) (x y : ℝ) :
    (cheb n a).eval x y = PoissonR3.T n (a.eval x y) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cheb,PoissonR3.T,Expr.eval]
  | one => rfl
  | more n h0 h1 => simp [cheb,PoissonR3.T,h0,h1,Expr.eval]

def nExpr : Expr := bubble Expr.x * bubble Expr.y * ((Expr.rat (33653889/16777216)) +
  (Expr.rat (-12498155/16777216)) * Expr.tanh ((Expr.rat (10028835/16777216))*Expr.x+(Expr.rat (-15697194/16777216))*Expr.y+(Expr.rat (-6582840/16777216))) +
  (Expr.rat (12311660/16777216)) * Expr.tanh ((Expr.rat (-3130818/16777216))*Expr.x+(Expr.rat (21325544/16777216))*Expr.y+(Expr.rat (-9770752/16777216))) +
  (Expr.rat (-17419905/16777216)) * Expr.tanh ((Expr.rat (2687543/16777216))*Expr.x+(Expr.rat (16410348/16777216))*Expr.y+(Expr.rat (-36535174/16777216))) +
  (Expr.rat (-18087057/16777216)) * Expr.tanh ((Expr.rat (-663358/16777216))*Expr.x+(Expr.rat (-24569170/16777216))*Expr.y+(Expr.rat (27618223/16777216))) +
  (Expr.rat (-3965151/16777216)) * Expr.tanh ((Expr.rat (-4041981/16777216))*Expr.x+(Expr.rat (-3009566/16777216))*Expr.y+(Expr.rat (2549353/16777216))) +
  (Expr.rat (29531713/16777216)) * Expr.tanh ((Expr.rat (8636176/16777216))*Expr.x+(Expr.rat (-15380473/16777216))*Expr.y+(Expr.rat (18162178/16777216))) +
  (Expr.rat (16099143/16777216)) * Expr.tanh ((Expr.rat (-5106673/16777216))*Expr.x+(Expr.rat (3928507/16777216))*Expr.y+(Expr.rat (15874471/16777216))) +
  (Expr.rat (11711319/16777216)) * Expr.tanh ((Expr.rat (7559742/16777216))*Expr.x+(Expr.rat (-3179262/16777216))*Expr.y+(Expr.rat (18205620/16777216))) +
  (Expr.rat (-36544829/16777216)) * Expr.tanh ((Expr.rat (-19705717/16777216))*Expr.x+(Expr.rat (-26808326/16777216))*Expr.y+(Expr.rat (62892144/16777216))) +
  (Expr.rat (25901550/16777216)) * Expr.tanh ((Expr.rat (8815791/16777216))*Expr.x+(Expr.rat (-9856854/16777216))*Expr.y+(Expr.rat (3435363/16777216))) +
  (Expr.rat (-10758100/16777216)) * Expr.tanh ((Expr.rat (-12082314/16777216))*Expr.x+(Expr.rat (11617157/16777216))*Expr.y+(Expr.rat (4421606/16777216))) +
  (Expr.rat (7035087/16777216)) * Expr.tanh ((Expr.rat (-6705311/16777216))*Expr.x+(Expr.rat (10513409/16777216))*Expr.y+(Expr.rat (9029355/16777216))) +
  (Expr.rat (-2900717/16777216)) * Expr.tanh ((Expr.rat (-2324014/16777216))*Expr.x+(Expr.rat (-3725155/16777216))*Expr.y+(Expr.rat (-4407648/16777216))) +
  (Expr.rat (18808434/16777216)) * Expr.tanh ((Expr.rat (-14904796/16777216))*Expr.x+(Expr.rat (-304757/16777216))*Expr.y+(Expr.rat (-4749268/16777216))) +
  (Expr.rat (-27769719/16777216)) * Expr.tanh ((Expr.rat (-14440123/16777216))*Expr.x+(Expr.rat (-19046938/16777216))*Expr.y+(Expr.rat (49964766/16777216))) +
  (Expr.rat (6561356/16777216)) * Expr.tanh ((Expr.rat (-4170089/16777216))*Expr.x+(Expr.rat (6779566/16777216))*Expr.y+(Expr.rat (9261507/16777216))))

def cExpr : Expr := bubble Expr.x * bubble Expr.y * ((Expr.rat (-114867262/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (62159804/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-168867553/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (41678863/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-86185053/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (-20277005/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (-27389138/1099511627776)) * cheb 0 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (-476900472/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (-997341545/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-405836774/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (-662624015/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-88354583/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (23204417/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (14878903/1099511627776)) * cheb 1 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (-202954182/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (117567576/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-315753791/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (57021435/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-120417951/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (-67310150/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (-23760326/1099511627776)) * cheb 2 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (-259431907/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (-477532559/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-263697813/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (-352309607/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-127897494/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (-25468296/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (-4886241/1099511627776)) * cheb 3 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (-93900003/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (27202392/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-122713092/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (-80569815/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-38562128/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (-8248970/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (-874640/1099511627776)) * cheb 4 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (107049604/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (-24072645/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-43611416/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (-15515650/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-4615678/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (-938550/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (20939/1099511627776)) * cheb 5 (2*Expr.x-1) * cheb 6 (2*Expr.y-1) +
  (Expr.rat (-1715638/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 0 (2*Expr.y-1) +
  (Expr.rat (-7051765/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 1 (2*Expr.y-1) +
  (Expr.rat (-7873644/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 2 (2*Expr.y-1) +
  (Expr.rat (-2673671/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 3 (2*Expr.y-1) +
  (Expr.rat (-455592/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 4 (2*Expr.y-1) +
  (Expr.rat (205163/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 5 (2*Expr.y-1) +
  (Expr.rat (10147/1099511627776)) * cheb 6 (2*Expr.x-1) * cheb 6 (2*Expr.y-1))

def fExpr : Expr := Expr.exp (Expr.x*Expr.y) *
  (2*(bubble Expr.x+bubble Expr.y)-
   2*(Expr.y*bubble Expr.y*dbubble Expr.x+Expr.x*bubble Expr.x*dbubble Expr.y)-
   bubble Expr.x*bubble Expr.y*(Expr.x*Expr.x+Expr.y*Expr.y))

theorem nExpr_eq (x y : ℝ) : nExpr.eval x y = PoissonR3.N x y := by
  norm_num [nExpr,PoissonR3.N,bubble,PoissonPilot.p,Expr.eval,sub_eq_add_neg]

theorem cExpr_eq (x y : ℝ) : cExpr.eval x y = PoissonR3.C x y := by
  simp only [cExpr,Expr.eval_mul,Expr.eval_add,eval_cheb]
  norm_num [PoissonR3.C,bubble,PoissonPilot.p,Expr.eval,sub_eq_add_neg]

theorem fExpr_eq (x y : ℝ) : fExpr.eval x y = PoissonR3.forcing x y := by
  norm_num [fExpr,PoissonR3.forcing,bubble,dbubble,PoissonPilot.p,PoissonPilot.dp,Expr.eval,pow_two,sub_eq_add_neg]

def corrected : Expr := nExpr-cExpr

def residual : Expr :=
  -((corrected.diff false).diff false + (corrected.diff true).diff true)-fExpr

theorem residual_eq (x y : ℝ) : residual.eval x y =
    -PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y - PoissonR3.forcing x y := by
  have h : (fun a b => PoissonR3.N a b-PoissonR3.C a b) = corrected.eval := by
    funext a b
    simp [corrected,nExpr_eq,cExpr_eq]
  rw [h]
  simp only [residual,Expr.eval_sub,Expr.eval_neg,Expr.eval_add,PoissonR3.Lap,
    Expr.deriv2_eval_x,Expr.deriv2_eval_y,fExpr_eq]

#check nExpr_eq
#check cExpr_eq
#check residual_eq
#print axioms nExpr_eq
#print axioms cExpr_eq
#print axioms residual_eq
end PinnCert
