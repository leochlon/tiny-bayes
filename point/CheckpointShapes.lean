import Bridge
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def MatrixShape (m n : Nat) (A : List (List ℝ)) : Prop :=
  A.length = m ∧ ∀ row ∈ A, row.length = n

theorem packed_matrix_shape (m n : Nat) (rs : List Nat) (h : rs.length = m) :
    MatrixShape m n (CON.mat n rs) := by
  constructor
  · simpa [CON.mat] using h
  · intro row hr
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr
    exact row_length _ _

def LayerShape (L : CON.Layer) : Prop :=
  L.ln1g.length = 128 ∧ L.ln1b.length = 128 ∧
  L.ln2g.length = 128 ∧ L.ln2b.length = 128 ∧
  MatrixShape 384 128 L.qkvW ∧ L.qkvB.length = 384 ∧
  MatrixShape 128 128 L.oW ∧ L.oB.length = 128 ∧
  MatrixShape 512 128 L.fW ∧ L.fB.length = 512 ∧
  MatrixShape 128 512 L.pW ∧ L.pB.length = 128

theorem layer0_shape : LayerShape CON.layer0 := by
  simp only [LayerShape, CON.layer0, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L0.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L0.oW_length,
    packed_matrix_shape _ _ _ CON.W.L0.fW_length,
    packed_matrix_shape _ _ _ CON.W.L0.pW_length⟩

theorem layer1_shape : LayerShape CON.layer1 := by
  simp only [LayerShape, CON.layer1, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L1.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L1.oW_length,
    packed_matrix_shape _ _ _ CON.W.L1.fW_length,
    packed_matrix_shape _ _ _ CON.W.L1.pW_length⟩

theorem layer2_shape : LayerShape CON.layer2 := by
  simp only [LayerShape, CON.layer2, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L2.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L2.oW_length,
    packed_matrix_shape _ _ _ CON.W.L2.fW_length,
    packed_matrix_shape _ _ _ CON.W.L2.pW_length⟩

theorem layer3_shape : LayerShape CON.layer3 := by
  simp only [LayerShape, CON.layer3, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L3.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L3.oW_length,
    packed_matrix_shape _ _ _ CON.W.L3.fW_length,
    packed_matrix_shape _ _ _ CON.W.L3.pW_length⟩

theorem layer4_shape : LayerShape CON.layer4 := by
  simp only [LayerShape, CON.layer4, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L4.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L4.oW_length,
    packed_matrix_shape _ _ _ CON.W.L4.fW_length,
    packed_matrix_shape _ _ _ CON.W.L4.pW_length⟩

theorem layer5_shape : LayerShape CON.layer5 := by
  simp only [LayerShape, CON.layer5, row_length, true_and, and_true]
  exact ⟨packed_matrix_shape _ _ _ CON.W.L5.qkvW_length,
    packed_matrix_shape _ _ _ CON.W.L5.oW_length,
    packed_matrix_shape _ _ _ CON.W.L5.fW_length,
    packed_matrix_shape _ _ _ CON.W.L5.pW_length⟩

theorem actual_six_layer_shapes :
    CON.pythia14m.layers.length = 6 ∧ ∀ L ∈ CON.pythia14m.layers, LayerShape L := by
  constructor
  · rfl
  · intro L h
    simp only [CON.pythia14m, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact layer0_shape
    · exact layer1_shape
    · exact layer2_shape
    · exact layer3_shape
    · exact layer4_shape
    · exact layer5_shape

theorem actual_vocabulary_row_widths (j : Fin 50304) :
    (CON.pythia14m.emb j).length = 128 ∧ (CON.pythia14m.unemb j).length = 128 := by
  exact ⟨row_length _ _, row_length _ _⟩

theorem input_table_row_count : (CON.W.eChunks.map List.length).sum = 50304 := by
  decide +kernel
theorem output_table_row_count : (CON.W.uChunks.map List.length).sum = 50304 := by
  decide +kernel

#check actual_six_layer_shapes
#print axioms actual_six_layer_shapes
#check actual_vocabulary_row_widths
#print axioms actual_vocabulary_row_widths
#print axioms input_table_row_count
#print axioms output_table_row_count
end PythiaCert
