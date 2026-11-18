import WitnessLayer0
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Frame.L0
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer0 input
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, input_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer0 witnessInput
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, witnessInput_length]
end Frame.L0
namespace Frame.L1
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer1 Frame.L0.cstate
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, Frame.L0.cstate_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer1 Frame.L0.wstate
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, Frame.L0.wstate_length]
end Frame.L1
namespace Frame.L2
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer2 Frame.L1.cstate
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, Frame.L1.cstate_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer2 Frame.L1.wstate
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, Frame.L1.wstate_length]
end Frame.L2
namespace Frame.L3
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer3 Frame.L2.cstate
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, Frame.L2.cstate_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer3 Frame.L2.wstate
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, Frame.L2.wstate_length]
end Frame.L3
namespace Frame.L4
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer4 Frame.L3.cstate
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, Frame.L3.cstate_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer4 Frame.L3.wstate
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, Frame.L3.wstate_length]
end Frame.L4
namespace Frame.L5
noncomputable def cstate : List (List ℝ) := CON.layer CON.layer5 Frame.L4.cstate
theorem cstate_length : cstate.length = 32 := by
  simp only [cstate, CON.layer, List.length_map, List.length_range, Frame.L4.cstate_length]
noncomputable def wstate : List (List ℝ) := CON.layer CON.layer5 Frame.L4.wstate
theorem wstate_length : wstate.length = 32 := by
  simp only [wstate, CON.layer, List.length_map, List.length_range, Frame.L4.wstate_length]
end Frame.L5
theorem center_hidden_eq : CON.lastHidden CON.pythia14m tokens =
    CON.layerNorm CON.pythia14m.lnfg CON.pythia14m.lnfb (Frame.L5.cstate.getD 31 []) := rfl

theorem witness_hidden_eq : CON.lastHiddenFrom CON.pythia14m witnessInput =
    CON.layerNorm CON.pythia14m.lnfg CON.pythia14m.lnfb (Frame.L5.wstate.getD 31 []) := by
  simp only [CON.lastHiddenFrom, witnessInput_length]
  rfl
#print axioms center_hidden_eq
#print axioms witness_hidden_eq
end PythiaCert
