import Layer0Prefix
import FullInterval
import frozen.WitnessDomain
import PointChecks.L0.P32Q
import WitnessAttentionCheck
import WitnessHiddenCheck
import WitnessOutputCheck

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def witnessDelta : List ℝ := WitnessDomain.numerators.map PRO.wt
noncomputable def witness31 : List ℝ := CON.vadd input31 witnessDelta
noncomputable def witnessInput : List (List ℝ) := input.take 31 ++ [witness31]
noncomputable def witnessNorm : List (List ℝ) :=
  witnessInput.map (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b)

theorem witness31_length : witness31.length = 128 := by
  simp [witness31, CON.vadd, witnessDelta, WitnessDomain.coordinate_count, input31_length]
theorem witnessInput_length : witnessInput.length = 32 := by
  simp [witnessInput, input_length]
theorem witnessNorm_length : witnessNorm.length = 32 := by
  simp [witnessNorm, witnessInput_length]

theorem witness_input_check : PRO.allSub
    (PRO.vaddI (embeddingBox 329) (WitnessDomain.numerators.map PRO.ofW)) Point.L0P32.x = true := by
  decide +kernel

theorem witness31_mem : List.Forall₂ (PRO.memAt PRO.S) witness31 Point.L0P32.x :=
  f2_sub (PRO.f2_vadd (embedding_sound 329) (PRO.f2_wt WitnessDomain.numerators)) _ witness_input_check

theorem witness_q_mem : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b witness31)) Point.L0P32.q := by
  rw [← layer0_decode]
  exact qCheck_sound _ witness31_length witness31_mem Point.L0P32.q_check

theorem witness_all_q_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S))
    (witnessNorm.map (CON.qkv CON.layer0)) (layer0_q.take 31 ++ [Point.L0P32.q]) := by
  have hp := List.forall₂_take 31 all32_qkv_mem
  have h := PRO.f2_append hp (List.Forall₂.cons witness_q_mem List.Forall₂.nil)
  simpa only [witnessNorm, witnessInput, layer0Norm, List.map_append, List.map_cons, List.map_nil,
    CON.take_map_eq, List.map_map, Function.comp_def] using h

theorem witness_attention_mem : List.Forall₂ (PRO.memAt PRO.S)
    (CON.attnOut CON.layer0 witnessNorm 31) Point.L0P32.a := by
  rw [← layer0_decode, CompletionBridge.attnOut_eq _ layer0_qkv_rows _ _
    (by rw [witnessNorm_length]; decide)]
  have hq := List.forall₂_take 32 witness_all_q_mem
  rw [← layer0_decode] at hq
  have h := PRO.f2_attn (PRO.LL 0) 31 hq
  have ht : (layer0_q.take 31 ++ [Point.L0P32.q]).take 32 = layer0_q.take 31 ++ [Point.L0P32.q] := rfl
  rw [ht] at h
  exact f2_sub h _ witness_attention_check

noncomputable def witnessFC : List ℝ := CON.vadd
  (CON.mv CON.layer0.fW (CON.layerNorm CON.layer0.ln2g CON.layer0.ln2b witness31)) CON.layer0.fB

theorem witness_hidden_mem : List.Forall₂ (PRO.memAt PRO.S)
    (witnessFC.map CON.gelu) Point.L0P32.h := by
  have h := hidden_sound (PRO.LL 0) witness31_length witness31_mem
  have hc := witness_hidden_check
  simp only [PRO.hCheck, PRO.stList_eq] at hc
  exact f2_sub h _ hc

theorem witness_output_mem : List.Forall₂ (PRO.memAt PRO.S)
    (CON.vadd (CON.vadd witness31 (CON.attnOut CON.layer0 witnessNorm 31))
      (CON.mlpOut CON.layer0 (CON.layerNorm CON.layer0.ln2g CON.layer0.ln2b witness31))) Point.L0P32.o := by
  have hm := lin_sound CON.W.L0.pW 512 CON.W.L0.pB 128 witness_hidden_mem
  have h := PRO.f2_vadd (PRO.f2_vadd witness31_mem witness_attention_mem) hm
  exact f2_sub h _ witness_output_check

theorem witness_output_valid : ∀ B ∈ Point.L0P32.o, B.ok = true := by decide +kernel

theorem actual_witness_layer0_lastrow_enclosed : List.Forall₂ Encloses
    ((CON.layer CON.layer0 witnessInput).getD 31 []) Point.L0P32.o := by
  change List.Forall₂ Encloses
    (CON.vadd (CON.vadd witness31 (CON.attnOut CON.layer0 witnessNorm 31))
      (CON.mlpOut CON.layer0 (CON.layerNorm CON.layer0.ln2g CON.layer0.ln2b witness31))) Point.L0P32.o
  exact discharge_valid witness_output_mem witness_output_valid

theorem witness_delta_bound (z : ℝ) (hz : z ∈ witnessDelta) : |z| ≤ (37/16384 : ℝ) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  exact abs_le.mpr (WitnessDomain.scaled_envelope a ha)

theorem witness_delta_attains : |witnessDelta.getD 2 0| = (37/16384 : ℝ) := by
  norm_num [witnessDelta, WitnessDomain.numerators, PRO.wt]

#check actual_witness_layer0_lastrow_enclosed
#print axioms actual_witness_layer0_lastrow_enclosed
#print axioms witness_delta_bound
#print axioms witness_delta_attains
end PythiaCert
