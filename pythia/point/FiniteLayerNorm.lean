import CON.Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

namespace FiniteLN
open scoped BigOperators

noncomputable def mean (x : Fin 128 → ℝ) : ℝ := (∑ i,x i)/128
noncomputable def variance (x : Fin 128 → ℝ) : ℝ := (∑ i,(x i-mean x)^2)/128+1/100000
noncomputable def norm (g b x : Fin 128 → ℝ) (i : Fin 128) : ℝ :=
  g i*((x i-mean x)/(Real.sqrt (variance x)))+b i

theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith,List.length_ofFn,Nat.min_self]
  · intro i hi hj
    simp only [List.getElem_zipWith,List.getElem_ofFn]

theorem layerNorm_ofFn (g b x : Fin 128 → ℝ) :
    CON.layerNorm (List.ofFn g) (List.ofFn b) (List.ofFn x) = List.ofFn (norm g b x) := by
  simp only [CON.layerNorm,List.length_ofFn,Nat.cast_ofNat,List.sum_ofFn,List.map_ofFn,
    CON.vadd,zipWith_ofFn]
  rfl

#print axioms layerNorm_ofFn
end FiniteLN
