import PRO.Interval

/-! Strict evaluation for the kernel. `stX v k` equals `k v` (`stX_eq`), but its definition
makes the kernel reduce `v` to a literal once, before `k` uses it; without it a value that is used
several times is recomputed at every use. Core Lean only. -/

namespace PRO

def stNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem stNat_eq {α : Type} (n : Nat) (k : Nat → α) : stNat n k = k n := by
  cases n <;> rfl

def stInt {α : Type} (z : Int) (k : Int → α) : α :=
  match z with
  | Int.ofNat n => stNat n fun n' => k (Int.ofNat n')
  | Int.negSucc n => stNat n fun n' => k (Int.negSucc n')

theorem stInt_eq {α : Type} (z : Int) (k : Int → α) : stInt z k = k z := by
  cases z <;> simp [stInt, stNat_eq]

def stBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with
  | true => k true
  | false => k false

theorem stBool_eq {α : Type} (b : Bool) (k : Bool → α) : stBool b k = k b := by
  cases b <;> rfl

def stIv {α : Type} (X : Iv) (k : Iv → α) : α :=
  stInt X.lo fun a => stInt X.hi fun b => stBool X.ok fun o => k ⟨a, b, o⟩

theorem stIv_eq {α : Type} (X : Iv) (k : Iv → α) : stIv X k = k X := by
  cases X
  simp [stIv, stInt_eq, stBool_eq]

def stList {α : Type} : List Iv → (List Iv → α) → α
  | [], k => k []
  | X :: Xs, k => stIv X fun X' => stList Xs fun Xs' => k (X' :: Xs')

theorem stList_eq {α : Type} : ∀ (Xs : List Iv) (k : List Iv → α), stList Xs k = k Xs
  | [], _ => rfl
  | X :: Xs, k => by simp [stList, stIv_eq, stList_eq Xs]

def stLL {α : Type} : List (List Iv) → (List (List Iv) → α) → α
  | [], k => k []
  | X :: Xs, k => stList X fun X' => stLL Xs fun Xs' => k (X' :: Xs')

theorem stLL_eq {α : Type} : ∀ (Xs : List (List Iv)) (k : List (List Iv) → α), stLL Xs k = k Xs
  | [], _ => rfl
  | X :: Xs, k => by simp [stLL, stList_eq, stLL_eq Xs]

end PRO
