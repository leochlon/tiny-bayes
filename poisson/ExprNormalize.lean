import Mathlib.Tactic.SplitIfs
import ExprInterval

namespace PinnCert.Expr

def addC : Expr → Expr → Expr
  | .rat p, .rat q => .rat (p+q)
  | .rat p, b => if p=0 then b else .add (.rat p) b
  | a, .rat q => if q=0 then a else .add a (.rat q)
  | a,b => .add a b

def mulC : Expr → Expr → Expr
  | .rat p, .rat q => .rat (p*q)
  | .rat p, b => if p=0 then 0 else if p=1 then b else .mul (.rat p) b
  | a, .rat q => if q=0 then 0 else if q=1 then a else .mul a (.rat q)
  | a,b => .mul a b

def negC : Expr → Expr
  | .rat q => .rat (-q)
  | .neg a => a
  | a => .neg a

@[simp] theorem eval_addC (a b : Expr) (x y : ℝ) :
    (addC a b).eval x y = a.eval x y + b.eval x y := by
  cases a <;> cases b <;> simp [addC,eval] <;> split_ifs <;> simp_all [eval]

@[simp] theorem eval_mulC (a b : Expr) (x y : ℝ) :
    (mulC a b).eval x y = a.eval x y * b.eval x y := by
  cases a <;> cases b <;> simp [mulC,eval] <;> split_ifs <;> simp_all [eval]

@[simp] theorem eval_negC (a : Expr) (x y : ℝ) :
    (negC a).eval x y = -a.eval x y := by
  cases a <;> simp [negC,eval]

def normalize : Expr → Expr
  | .rat q => .rat q
  | .x => .x
  | .y => .y
  | .add a b => addC (normalize a) (normalize b)
  | .neg a => negC (normalize a)
  | .mul a b => mulC (normalize a) (normalize b)
  | .exp a => .exp (normalize a)
  | .tanh a => .tanh (normalize a)

@[simp] theorem normalize_sound (e : Expr) (x y : ℝ) :
    e.normalize.eval x y = e.eval x y := by
  induction e with
  | rat q => rfl
  | x => rfl
  | y => rfl
  | add a b ha hb => simpa only [normalize,eval_addC,eval,ha,hb]
  | neg a ha => simpa only [normalize,eval_negC,eval,ha]
  | mul a b ha hb => simpa only [normalize,eval_mulC,eval,ha,hb]
  | exp a ha => simp only [normalize,eval,ha]
  | tanh a ha => simp only [normalize,eval,ha]

def ndiff (axis : Bool) (e : Expr) := (e.diff axis).normalize

theorem hasDerivAt_ndiff_x (e : Expr) (x y : ℝ) :
    HasDerivAt (fun t => e.eval t y) ((e.ndiff false).eval x y) x := by
  simpa [ndiff] using e.hasDerivAt_eval_x x y

theorem hasDerivAt_ndiff_y (e : Expr) (x y : ℝ) :
    HasDerivAt (fun t => e.eval x t) ((e.ndiff true).eval x y) y := by
  simpa [ndiff] using e.hasDerivAt_eval_y x y

#print axioms normalize_sound
#print axioms hasDerivAt_ndiff_x
end PinnCert.Expr
