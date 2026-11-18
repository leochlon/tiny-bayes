import ExprInterval

namespace PinnDAG
open PinnCert

inductive Instr where
  | rat : ℚ → Instr
  | x : Instr
  | y : Instr
  | add : ℕ → ℕ → Instr
  | neg : ℕ → Instr
  | mul : ℕ → ℕ → Instr
  | exp : ℕ → Instr
  | tanh : ℕ → Instr
  deriving Repr, DecidableEq

def Instr.expr : Instr → List Expr → Expr
  | .rat q, _ => .rat q
  | .x, _ => .x
  | .y, _ => .y
  | .add a b, es => .add (es.getD a (.rat 0)) (es.getD b (.rat 0))
  | .neg a, es => .neg (es.getD a (.rat 0))
  | .mul a b, es => .mul (es.getD a (.rat 0)) (es.getD b (.rat 0))
  | .exp a, es => .exp (es.getD a (.rat 0))
  | .tanh a, es => .tanh (es.getD a (.rat 0))

def Instr.interval : Instr → Iv → Iv → List Iv → Iv
  | .rat q, _, _, _ => ratI q
  | .x, X, _, _ => X
  | .y, _, Y, _ => Y
  | .add a b, _, _, vs => PinnCert.add (vs.getD a zero) (vs.getD b zero)
  | .neg a, _, _, vs => PinnCert.neg (vs.getD a zero)
  | .mul a b, _, _, vs => PinnCert.mul (vs.getD a zero) (vs.getD b zero)
  | .exp a, _, _, vs => expI (vs.getD a zero)
  | .tanh a, _, _, vs => tanhI (vs.getD a zero)

def exprRun : List Instr → List Expr → List Expr
  | [], es => es
  | i::code, es => exprRun code (i.expr es :: es)

def resultRun : List Iv → List Iv → List Iv
  | [], vs => vs
  | v::data, vs => resultRun data (v::vs)

def ivEq (a b : Iv) : Bool :=
  decide (a.lo=b.lo) && decide (a.hi=b.hi) && decide (a.ok=b.ok)

theorem ivEq_sound {a b : Iv} (h : ivEq a b = true) : a=b := by
  cases a with
  | mk al ah ao =>
    cases b with
    | mk bl bh bo =>
      simp only [ivEq, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hl,hh⟩,ho⟩ := h
      simp_all

def check : List Instr → List Iv → Iv → Iv → List Iv → Bool
  | [], [], _, _, _ => true
  | i::code, v::data, X, Y, vs =>
      ivEq (i.interval X Y vs) v && check code data X Y (v::vs)
  | _, _, _, _, _ => false

/-- The semantic invariant includes out-of-range indices via matching zero defaults. -/
def EnvRel (x y : ℝ) (es : List Expr) (vs : List Iv) : Prop :=
  ∀ i, memAt S ((es.getD i (.rat 0)).eval x y) (vs.getD i zero)

theorem EnvRel.cons {x y : ℝ} {es : List Expr} {vs : List Iv} {e : Expr} {v : Iv}
    (h : EnvRel x y es vs) (he : memAt S (e.eval x y) v) :
    EnvRel x y (e::es) (v::vs) := by
  intro i
  cases i with
  | zero => simpa using he
  | succ n => simpa using h n

theorem EnvRel.nil (x y : ℝ) : EnvRel x y [] [] := by
  intro i
  simp only [List.getD_nil, Expr.eval]
  intro _
  norm_num [PinnCert.zero]

theorem Instr.sound (i : Instr) {x y : ℝ} {es : List Expr} {vs : List Iv} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y) (henv : EnvRel x y es vs) :
    memAt S ((i.expr es).eval x y) (i.interval X Y vs) := by
  cases i with
  | rat q => exact memAt_rat q
  | x => exact hx
  | y => exact hy
  | add a b => exact memAt_add (henv a) (henv b)
  | neg a => exact memAt_neg (henv a)
  | mul a b => exact memAt_mul (henv a) (henv b)
  | exp a => exact memAt_exp (henv a)
  | tanh a => exact memAt_tanh (henv a)

theorem check_sound (code : List Instr) {data : List Iv} {x y : ℝ}
    {es : List Expr} {vs : List Iv} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y) (henv : EnvRel x y es vs)
    (hcheck : check code data X Y vs = true) :
    EnvRel x y (exprRun code es) (resultRun data vs) := by
  induction code generalizing data es vs with
  | nil =>
    cases data with
    | nil => exact henv
    | cons v data => simp [check] at hcheck
  | cons i code ih =>
    cases data with
    | nil => simp [check] at hcheck
    | cons v data =>
      simp only [check, Bool.and_eq_true] at hcheck
      have hv : memAt S ((i.expr es).eval x y) v := by
        rw [← ivEq_sound hcheck.1]
        exact i.sound hx hy henv
      change EnvRel x y (exprRun code (i.expr es :: es)) (resultRun data (v::vs))
      exact ih (data := data) (es := i.expr es :: es) (vs := v::vs) (henv.cons hv) hcheck.2

theorem check_from_nil (code : List Instr) {data : List Iv} {x y : ℝ} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y)
    (hcheck : check code data X Y [] = true) (i : ℕ) :
    memAt S (((exprRun code []).getD i (.rat 0)).eval x y)
      ((resultRun data []).getD i zero) :=
  check_sound code hx hy (EnvRel.nil x y) hcheck i

theorem check_encloses (code : List Instr) {data : List Iv} {x y : ℝ} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y)
    (hcheck : check code data X Y [] = true) (i : ℕ)
    (hok : ((resultRun data []).getD i zero).ok = true) :
    (((resultRun data []).getD i zero).lo : ℝ) ≤
      ((exprRun code []).getD i (.rat 0)).eval x y * S ∧
    ((exprRun code []).getD i (.rat 0)).eval x y * S ≤
      (((resultRun data []).getD i zero).hi : ℝ) :=
  check_from_nil code hx hy hcheck i hok

theorem check_cons_of_eq {i : Instr} {code : List Instr} {v : Iv} {data : List Iv}
    {X Y : Iv} {vs : List Iv}
    (hstep : i.interval X Y vs = v) (hrest : check code data X Y (v::vs) = true) :
    check (i::code) (v::data) X Y vs = true := by
  simp only [check, hstep, ivEq, decide_true, Bool.true_and, hrest]

theorem resultRun_eq (data vs : List Iv) : resultRun data vs = data.reverse ++ vs := by
  induction data generalizing vs with
  | nil => simp [resultRun]
  | cons v data ih => simp [resultRun, ih, List.reverse_cons, List.append_assoc]

theorem check_length (code : List Instr) {data : List Iv} {X Y : Iv} {vs : List Iv}
    (hcheck : check code data X Y vs = true) : code.length=data.length := by
  induction code generalizing data vs with
  | nil => cases data <;> simp_all [check]
  | cons i code ih =>
    cases data with
    | nil => simp [check] at hcheck
    | cons v data =>
      simp only [check, Bool.and_eq_true] at hcheck
      simp only [List.length_cons, ih hcheck.2]

#print axioms Instr.sound
#print axioms check_sound
#print axioms check_from_nil
#print axioms check_length
#print axioms check_encloses
#print axioms check_cons_of_eq
#check check_from_nil
end PinnDAG
