import CheckpointShapes
import FixedPrefix
import WitnessNorm

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The unchanged128-coordinate perturbation domain of the full32-token model. -/
noncomputable def perturbInput (δ : Fin 128 → ℝ) : List (List ℝ) :=
  fixedPrefixInput ++ [CON.vadd input31 (List.ofFn δ)]

theorem perturbInput_length (δ : Fin 128 → ℝ) : (perturbInput δ).length = 32 := by
  simp [perturbInput, fixedPrefixInput_length]

theorem perturbInput_rows (δ : Fin 128 → ℝ) : ∀ x ∈ perturbInput δ, x.length = 128 := by
  intro x hx
  simp only [perturbInput, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl
  · have hm : x ∈ input := List.mem_of_mem_take hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hm
    exact row_length _ _
  · simp only [CON.vadd, List.length_zipWith, input31_length, List.length_ofFn, Nat.min_self]

theorem witnessInput_eq_perturbInput : witnessInput = perturbInput witnessVector :=
  witnessInput_eq_vector

theorem layer_preserves_length (L : CON.Layer) (xs : List (List ℝ)) :
    (CON.layer L xs).length = xs.length := by
  simp only [CON.layer, List.length_map, List.length_range]

theorem layer_preserves_width (L : CON.Layer) (hL : LayerShape L)
    {xs : List (List ℝ)} (hx : ∀ x ∈ xs, x.length = 128) :
    ∀ x ∈ CON.layer L xs, x.length = 128 := by
  rcases hL with ⟨_, _, _, _, _, _, ho, hob, _, _, hp, hpb⟩
  intro x hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
  have hi' := List.mem_range.mp hi
  have hrow : (xs.getD i []).length = 128 := by
    rw [List.getD_eq_getElem _ _ hi']
    exact hx _ (List.getElem_mem _)
  simp only [CON.vadd, CON.attnOut, CON.mlpOut, CON.mv,
    List.length_zipWith, List.length_map, ho.1, hob, hp.1, hpb,
    hrow, Nat.min_self]

theorem fold_preserves_length (Ls : List CON.Layer) (xs : List (List ℝ)) :
    (Ls.foldl (fun H L => CON.layer L H) xs).length = xs.length := by
  induction Ls generalizing xs with
  | nil => rfl
  | cons L Ls ih =>
    simpa only [List.foldl_cons, layer_preserves_length] using ih (CON.layer L xs)

theorem fold_preserves_width (Ls : List CON.Layer)
    (hLs : ∀ L ∈ Ls, LayerShape L) {xs : List (List ℝ)}
    (hx : ∀ x ∈ xs, x.length = 128) :
    ∀ x ∈ Ls.foldl (fun H L => CON.layer L H) xs, x.length = 128 := by
  induction Ls generalizing xs with
  | nil => exact hx
  | cons L Ls ih =>
    apply ih (fun K hK => hLs K (by simp [hK]))
    exact layer_preserves_width L (hLs L (by simp)) hx

theorem actual_lastHiddenFrom_length {E : List (List ℝ)}
    (hE : E.length = 32) (hrows : ∀ x ∈ E, x.length = 128) :
    (CON.lastHiddenFrom CON.pythia14m E).length = 128 := by
  have hlen : (CON.hiddenFrom CON.pythia14m E).length = 32 := by
    simpa only [CON.hiddenFrom, hE] using fold_preserves_length CON.pythia14m.layers E
  have hwidth : ∀ x ∈ CON.hiddenFrom CON.pythia14m E, x.length = 128 :=
    fold_preserves_width _ actual_six_layer_shapes.2 hrows
  have hlast : ((CON.hiddenFrom CON.pythia14m E).getD 31 []).length = 128 := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; decide)]
    exact hwidth _ (List.getElem_mem _)
  have hg : CON.pythia14m.lnfg.length = 128 := row_length _ _
  have hb : CON.pythia14m.lnfb.length = 128 := row_length _ _
  simp only [CON.lastHiddenFrom, hE, show 32-1=31 from rfl, CON.layerNorm,
    CON.vadd, List.length_zipWith, hlast, hg, hb, Nat.min_self]

/-- Structural shape is discharged for every perturbation, independently of
the still-required numerical affine propagation. -/
theorem actual_perturbed_hidden_length (δ : Fin 128 → ℝ) :
    (CON.lastHiddenFrom CON.pythia14m (perturbInput δ)).length = 128 :=
  actual_lastHiddenFrom_length (perturbInput_length δ) (perturbInput_rows δ)

#check witnessInput_eq_perturbInput
#check actual_perturbed_hidden_length
#print axioms witnessInput_eq_perturbInput
#print axioms actual_perturbed_hidden_length
end PythiaCert
