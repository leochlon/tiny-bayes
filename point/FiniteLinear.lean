import FiniteLayerNorm
import CON.Pythia

namespace FiniteLinear
open scoped BigOperators
set_option maxRecDepth 100000

@[simp] theorem getD_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i.val d = f i := by
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ hi,List.getElem_ofFn]

noncomputable def rowFn {n : ℕ} (r : List ℝ) : Fin n → ℝ := fun i => r.getD i.val 0

theorem ofFn_rowFn {n : ℕ} (r : List ℝ) (hr : r.length = n) :
    List.ofFn (rowFn (n:=n) r) = r := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,hr]
  · intro i hi hj
    simp only [List.getElem_ofFn,rowFn,List.getD_eq_getElem r 0 hj]

theorem dot_ofFn {n : ℕ} (a b : Fin n → ℝ) :
    CON.dot (List.ofFn a) (List.ofFn b) = ∑ i,a i*b i := by
  rw [CON.dot,FiniteLN.zipWith_ofFn,List.sum_ofFn]

theorem linear_ofFn {m n : ℕ} (W : List (List ℝ)) (b : List ℝ) (x : Fin n → ℝ)
    (hW : W.length=m) (hb : b.length=m) (hrow : ∀r∈W,r.length=n) :
    CON.vadd (CON.mv W (List.ofFn x)) b = List.ofFn (fun i : Fin m =>
      (∑ j : Fin n, ((W.getD i.val []).getD j.val 0)*x j)+b.getD i.val 0) := by
  apply List.ext_getElem
  · simp only [CON.vadd,CON.mv,List.length_zipWith,List.length_map,hW,hb,List.length_ofFn,Nat.min_self]
  · intro i hi hj
    have him : i < m := by simpa only [List.length_ofFn] using hj
    have hiW : i < W.length := by omega
    have hib : i < b.length := by omega
    simp only [CON.vadd,CON.mv,List.getElem_zipWith,List.getElem_map,List.getElem_ofFn,
      List.getD_eq_getElem W [] hiW,List.getD_eq_getElem b 0 hib]
    have hr : (W[i]).length=n := hrow (W[i]) (List.getElem_mem _)
    rw [← ofFn_rowFn (W[i]) hr,dot_ofFn]
    simp only [getD_ofFn]

#print axioms linear_ofFn
end FiniteLinear
