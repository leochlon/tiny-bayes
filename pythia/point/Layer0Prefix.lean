import PointLink
import Shard
import Layer0Data
import PointChecks.L0.P0Q
import PointChecks.L0.P1Q
import PointChecks.L0.P2Q
import PointChecks.L0.P3Q
import PointChecks.L0.P4Q
import PointChecks.L0.P5Q
import PointChecks.L0.P6Q
import PointChecks.L0.P7Q
import PointChecks.L0.P8Q
import PointChecks.L0.P9Q
import PointChecks.L0.P10Q
import PointChecks.L0.P11Q
import PointChecks.L0.P12Q
import PointChecks.L0.P13Q
import PointChecks.L0.P14Q
import PointChecks.L0.P15Q
import PointChecks.L0.P16Q
import PointChecks.L0.P17Q
import PointChecks.L0.P18Q
import PointChecks.L0.P19Q
import PointChecks.L0.P20Q
import PointChecks.L0.P21Q
import PointChecks.L0.P22Q
import PointChecks.L0.P23Q
import PointChecks.L0.P24Q
import PointChecks.L0.P25Q
import PointChecks.L0.P26Q
import PointChecks.L0.P27Q
import PointChecks.L0.P28Q
import PointChecks.L0.P29Q
import PointChecks.L0.P30Q
import PointChecks.L0.P31Q
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem input0_check : PRO.allSub (embeddingBox 0) Point.L0P0.x = true := by decide +kernel
theorem prefix_q0_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 0))) Point.L0P0.q :=
  layer0_qCheck_sound 0 input0_check Point.L0P0.q_check
theorem prefix_q0_valid : ∀ B ∈ Point.L0P0.q, B.ok = true := by decide +kernel
theorem input1_check : PRO.allSub (embeddingBox 34) Point.L0P1.x = true := by decide +kernel
theorem prefix_q1_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 34))) Point.L0P1.q :=
  layer0_qCheck_sound 34 input1_check Point.L0P1.q_check
theorem prefix_q1_valid : ∀ B ∈ Point.L0P1.q, B.ok = true := by decide +kernel
theorem input2_check : PRO.allSub (embeddingBox 10166) Point.L0P2.x = true := by decide +kernel
theorem prefix_q2_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 10166))) Point.L0P2.q :=
  layer0_qCheck_sound 10166 input2_check Point.L0P2.q_check
theorem prefix_q2_valid : ∀ B ∈ Point.L0P2.q, B.ok = true := by decide +kernel
theorem input3_check : PRO.allSub (embeddingBox 11454) Point.L0P3.x = true := by decide +kernel
theorem prefix_q3_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 11454))) Point.L0P3.q :=
  layer0_qCheck_sound 11454 input3_check Point.L0P3.q_check
theorem prefix_q3_valid : ∀ B ∈ Point.L0P3.q, B.ok = true := by decide +kernel
theorem input4_check : PRO.allSub (embeddingBox 2990) Point.L0P4.x = true := by decide +kernel
theorem prefix_q4_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 2990))) Point.L0P4.q :=
  layer0_qCheck_sound 2990 input4_check Point.L0P4.q_check
theorem prefix_q4_valid : ∀ B ∈ Point.L0P4.q, B.ok = true := by decide +kernel
theorem input5_check : PRO.allSub (embeddingBox 8115) Point.L0P5.x = true := by decide +kernel
theorem prefix_q5_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 8115))) Point.L0P5.q :=
  layer0_qCheck_sound 8115 input5_check Point.L0P5.q_check
theorem prefix_q5_valid : ∀ B ∈ Point.L0P5.q, B.ok = true := by decide +kernel
theorem input6_check : PRO.allSub (embeddingBox 247) Point.L0P6.x = true := by decide +kernel
theorem prefix_q6_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 247))) Point.L0P6.q :=
  layer0_qCheck_sound 247 input6_check Point.L0P6.q_check
theorem prefix_q6_valid : ∀ B ∈ Point.L0P6.q, B.ok = true := by decide +kernel
theorem input7_check : PRO.allSub (embeddingBox 3425) Point.L0P7.x = true := by decide +kernel
theorem prefix_q7_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 3425))) Point.L0P7.q :=
  layer0_qCheck_sound 3425 input7_check Point.L0P7.q_check
theorem prefix_q7_valid : ∀ B ∈ Point.L0P7.q, B.ok = true := by decide +kernel
theorem input8_check : PRO.allSub (embeddingBox 273) Point.L0P8.x = true := by decide +kernel
theorem prefix_q8_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 273))) Point.L0P8.q :=
  layer0_qCheck_sound 273 input8_check Point.L0P8.q_check
theorem prefix_q8_valid : ∀ B ∈ Point.L0P8.q, B.ok = true := by decide +kernel
theorem input9_check : PRO.allSub (embeddingBox 21761) Point.L0P9.x = true := by decide +kernel
theorem prefix_q9_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 21761))) Point.L0P9.q :=
  layer0_qCheck_sound 21761 input9_check Point.L0P9.q_check
theorem prefix_q9_valid : ∀ B ∈ Point.L0P9.q, B.ok = true := by decide +kernel
theorem input10_check : PRO.allSub (embeddingBox 281) Point.L0P10.x = true := by decide +kernel
theorem prefix_q10_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 281))) Point.L0P10.q :=
  layer0_qCheck_sound 281 input10_check Point.L0P10.q_check
theorem prefix_q10_valid : ∀ B ∈ Point.L0P10.q, B.ok = true := by decide +kernel
theorem input11_check : PRO.allSub (embeddingBox 7363) Point.L0P11.x = true := by decide +kernel
theorem prefix_q11_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 7363))) Point.L0P11.q :=
  layer0_qCheck_sound 7363 input11_check Point.L0P11.q_check
theorem prefix_q11_valid : ∀ B ∈ Point.L0P11.q, B.ok = true := by decide +kernel
theorem input12_check : PRO.allSub (embeddingBox 323) Point.L0P12.x = true := by decide +kernel
theorem prefix_q12_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 323))) Point.L0P12.q :=
  layer0_qCheck_sound 323 input12_check Point.L0P12.q_check
theorem prefix_q12_valid : ∀ B ∈ Point.L0P12.q, B.ok = true := by decide +kernel
theorem input13_check : PRO.allSub (embeddingBox 253) Point.L0P13.x = true := by decide +kernel
theorem prefix_q13_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 253))) Point.L0P13.q :=
  layer0_qCheck_sound 253 input13_check Point.L0P13.q_check
theorem prefix_q13_valid : ∀ B ∈ Point.L0P13.q, B.ok = true := by decide +kernel
theorem input14_check : PRO.allSub (embeddingBox 1735) Point.L0P14.x = true := by decide +kernel
theorem prefix_q14_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 1735))) Point.L0P14.q :=
  layer0_qCheck_sound 1735 input14_check Point.L0P14.q_check
theorem prefix_q14_valid : ∀ B ∈ Point.L0P14.q, B.ok = true := by decide +kernel
theorem input15_check : PRO.allSub (embeddingBox 10669) Point.L0P15.x = true := by decide +kernel
theorem prefix_q15_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 10669))) Point.L0P15.q :=
  layer0_qCheck_sound 10669 input15_check Point.L0P15.q_check
theorem prefix_q15_valid : ∀ B ∈ Point.L0P15.q, B.ok = true := by decide +kernel
theorem input16_check : PRO.allSub (embeddingBox 15) Point.L0P16.x = true := by decide +kernel
theorem prefix_q16_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 15))) Point.L0P16.q :=
  layer0_qCheck_sound 15 input16_check Point.L0P16.q_check
theorem prefix_q16_valid : ∀ B ∈ Point.L0P16.q, B.ok = true := by decide +kernel
theorem input17_check : PRO.allSub (embeddingBox 844) Point.L0P17.x = true := by decide +kernel
theorem prefix_q17_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 844))) Point.L0P17.q :=
  layer0_qCheck_sound 844 input17_check Point.L0P17.q_check
theorem prefix_q17_valid : ∀ B ∈ Point.L0P17.q, B.ok = true := by decide +kernel
theorem input18_check : PRO.allSub (embeddingBox 476) Point.L0P18.x = true := by decide +kernel
theorem prefix_q18_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 476))) Point.L0P18.q :=
  layer0_qCheck_sound 476 input18_check Point.L0P18.q_check
theorem prefix_q18_valid : ∀ B ∈ Point.L0P18.q, B.ok = true := by decide +kernel
theorem input19_check : PRO.allSub (embeddingBox 7472) Point.L0P19.x = true := by decide +kernel
theorem prefix_q19_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 7472))) Point.L0P19.q :=
  layer0_qCheck_sound 7472 input19_check Point.L0P19.q_check
theorem prefix_q19_valid : ∀ B ∈ Point.L0P19.q, B.ok = true := by decide +kernel
theorem input20_check : PRO.allSub (embeddingBox 1798) Point.L0P20.x = true := by decide +kernel
theorem prefix_q20_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 1798))) Point.L0P20.q :=
  layer0_qCheck_sound 1798 input20_check Point.L0P20.q_check
theorem prefix_q20_valid : ∀ B ∈ Point.L0P20.q, B.ok = true := by decide +kernel
theorem input21_check : PRO.allSub (embeddingBox 14800) Point.L0P21.x = true := by decide +kernel
theorem prefix_q21_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 14800))) Point.L0P21.q :=
  layer0_qCheck_sound 14800 input21_check Point.L0P21.q_check
theorem prefix_q21_valid : ∀ B ∈ Point.L0P21.q, B.ok = true := by decide +kernel
theorem input22_check : PRO.allSub (embeddingBox 13) Point.L0P22.x = true := by decide +kernel
theorem prefix_q22_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 13))) Point.L0P22.q :=
  layer0_qCheck_sound 13 input22_check Point.L0P22.q_check
theorem prefix_q22_valid : ∀ B ∈ Point.L0P22.q, B.ok = true := by decide +kernel
theorem input23_check : PRO.allSub (embeddingBox 7277) Point.L0P23.x = true := by decide +kernel
theorem prefix_q23_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 7277))) Point.L0P23.q :=
  layer0_qCheck_sound 7277 input23_check Point.L0P23.q_check
theorem prefix_q23_valid : ∀ B ∈ Point.L0P23.q, B.ok = true := by decide +kernel
theorem input24_check : PRO.allSub (embeddingBox 13650) Point.L0P24.x = true := by decide +kernel
theorem prefix_q24_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 13650))) Point.L0P24.q :=
  layer0_qCheck_sound 13650 input24_check Point.L0P24.q_check
theorem prefix_q24_valid : ∀ B ∈ Point.L0P24.q, B.ok = true := by decide +kernel
theorem input25_check : PRO.allSub (embeddingBox 13) Point.L0P25.x = true := by decide +kernel
theorem prefix_q25_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 13))) Point.L0P25.q :=
  layer0_qCheck_sound 13 input25_check Point.L0P25.q_check
theorem prefix_q25_valid : ∀ B ∈ Point.L0P25.q, B.ok = true := by decide +kernel
theorem input26_check : PRO.allSub (embeddingBox 285) Point.L0P26.x = true := by decide +kernel
theorem prefix_q26_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 285))) Point.L0P26.q :=
  layer0_qCheck_sound 285 input26_check Point.L0P26.q_check
theorem prefix_q26_valid : ∀ B ∈ Point.L0P26.q, B.ok = true := by decide +kernel
theorem input27_check : PRO.allSub (embeddingBox 1071) Point.L0P27.x = true := by decide +kernel
theorem prefix_q27_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 1071))) Point.L0P27.q :=
  layer0_qCheck_sound 1071 input27_check Point.L0P27.q_check
theorem prefix_q27_valid : ∀ B ∈ Point.L0P27.q, B.ok = true := by decide +kernel
theorem input28_check : PRO.allSub (embeddingBox 10151) Point.L0P28.x = true := by decide +kernel
theorem prefix_q28_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 10151))) Point.L0P28.q :=
  layer0_qCheck_sound 10151 input28_check Point.L0P28.q_check
theorem prefix_q28_valid : ∀ B ∈ Point.L0P28.q, B.ok = true := by decide +kernel
theorem input29_check : PRO.allSub (embeddingBox 46234) Point.L0P29.x = true := by decide +kernel
theorem prefix_q29_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 46234))) Point.L0P29.q :=
  layer0_qCheck_sound 46234 input29_check Point.L0P29.q_check
theorem prefix_q29_valid : ∀ B ∈ Point.L0P29.q, B.ok = true := by decide +kernel
theorem input30_check : PRO.allSub (embeddingBox 15) Point.L0P30.x = true := by decide +kernel
theorem prefix_q30_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 15))) Point.L0P30.q :=
  layer0_qCheck_sound 15 input30_check Point.L0P30.q_check
theorem prefix_q30_valid : ∀ B ∈ Point.L0P30.q, B.ok = true := by decide +kernel
theorem input31_check : PRO.allSub (embeddingBox 329) Point.L0P31.x = true := by decide +kernel
theorem prefix_q31_sound : List.Forall₂ (PRO.memAt PRO.S)
    (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb 329))) Point.L0P31.q :=
  layer0_qCheck_sound 329 input31_check Point.L0P31.q_check
theorem prefix_q31_valid : ∀ B ∈ Point.L0P31.q, B.ok = true := by decide +kernel
noncomputable def layer0Norm : List (List ℝ) := input.map (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b)

theorem all32_qkv_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S))
    (layer0Norm.map (CON.qkv CON.layer0)) layer0_q := by
  exact List.Forall₂.cons prefix_q0_sound (List.Forall₂.cons prefix_q1_sound (List.Forall₂.cons prefix_q2_sound (List.Forall₂.cons prefix_q3_sound (List.Forall₂.cons prefix_q4_sound (List.Forall₂.cons prefix_q5_sound (List.Forall₂.cons prefix_q6_sound (List.Forall₂.cons prefix_q7_sound (List.Forall₂.cons prefix_q8_sound (List.Forall₂.cons prefix_q9_sound (List.Forall₂.cons prefix_q10_sound (List.Forall₂.cons prefix_q11_sound (List.Forall₂.cons prefix_q12_sound (List.Forall₂.cons prefix_q13_sound (List.Forall₂.cons prefix_q14_sound (List.Forall₂.cons prefix_q15_sound (List.Forall₂.cons prefix_q16_sound (List.Forall₂.cons prefix_q17_sound (List.Forall₂.cons prefix_q18_sound (List.Forall₂.cons prefix_q19_sound (List.Forall₂.cons prefix_q20_sound (List.Forall₂.cons prefix_q21_sound (List.Forall₂.cons prefix_q22_sound (List.Forall₂.cons prefix_q23_sound (List.Forall₂.cons prefix_q24_sound (List.Forall₂.cons prefix_q25_sound (List.Forall₂.cons prefix_q26_sound (List.Forall₂.cons prefix_q27_sound (List.Forall₂.cons prefix_q28_sound (List.Forall₂.cons prefix_q29_sound (List.Forall₂.cons prefix_q30_sound (List.Forall₂.cons prefix_q31_sound (List.Forall₂.nil))))))))))))))))))))))))))))))))
theorem actual_all32_layer0_qkv_enclosed : List.Forall₂ (List.Forall₂ Encloses)
    ((tokens.map CON.pythia14m.emb).map fun x => CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b x)) layer0_q := by
  exact List.Forall₂.cons (discharge_valid prefix_q0_sound prefix_q0_valid) (List.Forall₂.cons (discharge_valid prefix_q1_sound prefix_q1_valid) (List.Forall₂.cons (discharge_valid prefix_q2_sound prefix_q2_valid) (List.Forall₂.cons (discharge_valid prefix_q3_sound prefix_q3_valid) (List.Forall₂.cons (discharge_valid prefix_q4_sound prefix_q4_valid) (List.Forall₂.cons (discharge_valid prefix_q5_sound prefix_q5_valid) (List.Forall₂.cons (discharge_valid prefix_q6_sound prefix_q6_valid) (List.Forall₂.cons (discharge_valid prefix_q7_sound prefix_q7_valid) (List.Forall₂.cons (discharge_valid prefix_q8_sound prefix_q8_valid) (List.Forall₂.cons (discharge_valid prefix_q9_sound prefix_q9_valid) (List.Forall₂.cons (discharge_valid prefix_q10_sound prefix_q10_valid) (List.Forall₂.cons (discharge_valid prefix_q11_sound prefix_q11_valid) (List.Forall₂.cons (discharge_valid prefix_q12_sound prefix_q12_valid) (List.Forall₂.cons (discharge_valid prefix_q13_sound prefix_q13_valid) (List.Forall₂.cons (discharge_valid prefix_q14_sound prefix_q14_valid) (List.Forall₂.cons (discharge_valid prefix_q15_sound prefix_q15_valid) (List.Forall₂.cons (discharge_valid prefix_q16_sound prefix_q16_valid) (List.Forall₂.cons (discharge_valid prefix_q17_sound prefix_q17_valid) (List.Forall₂.cons (discharge_valid prefix_q18_sound prefix_q18_valid) (List.Forall₂.cons (discharge_valid prefix_q19_sound prefix_q19_valid) (List.Forall₂.cons (discharge_valid prefix_q20_sound prefix_q20_valid) (List.Forall₂.cons (discharge_valid prefix_q21_sound prefix_q21_valid) (List.Forall₂.cons (discharge_valid prefix_q22_sound prefix_q22_valid) (List.Forall₂.cons (discharge_valid prefix_q23_sound prefix_q23_valid) (List.Forall₂.cons (discharge_valid prefix_q24_sound prefix_q24_valid) (List.Forall₂.cons (discharge_valid prefix_q25_sound prefix_q25_valid) (List.Forall₂.cons (discharge_valid prefix_q26_sound prefix_q26_valid) (List.Forall₂.cons (discharge_valid prefix_q27_sound prefix_q27_valid) (List.Forall₂.cons (discharge_valid prefix_q28_sound prefix_q28_valid) (List.Forall₂.cons (discharge_valid prefix_q29_sound prefix_q29_valid) (List.Forall₂.cons (discharge_valid prefix_q30_sound prefix_q30_valid) (List.Forall₂.cons (discharge_valid prefix_q31_sound prefix_q31_valid) (List.Forall₂.nil))))))))))))))))))))))))))))))))
theorem layer0Norm_length : layer0Norm.length = 32 := by simp [layer0Norm, input, tokens]
theorem input_length : input.length = 32 := by simp [input, tokens]
theorem input_rows128 : ∀ x ∈ input, x.length = 128 := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact embedding_length t
#check actual_all32_layer0_qkv_enclosed
#print axioms actual_all32_layer0_qkv_enclosed
end PythiaCert
