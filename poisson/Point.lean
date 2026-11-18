import Candidate
import PointUnit0
import PointUnit1
import PointUnit2
import PointUnit3
import PointUnit4
import PointUnit5
import PointUnit6
import PointUnit7
import PointUnit8
import PointUnit9
import PointUnit10
import PointUnit11
import PointUnit12
import PointUnit13
import PointUnit14
import PointUnit15
import PointExp
namespace PoissonR3
open PoissonPilot
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem hpoint : N witness.1 witness.2-U witness.1 witness.2 ≤ -certL := by
  obtain ⟨hl0, hu0⟩ := point_tanh_0
  obtain ⟨hl1, hu1⟩ := point_tanh_1
  obtain ⟨hl2, hu2⟩ := point_tanh_2
  obtain ⟨hl3, hu3⟩ := point_tanh_3
  obtain ⟨hl4, hu4⟩ := point_tanh_4
  obtain ⟨hl5, hu5⟩ := point_tanh_5
  obtain ⟨hl6, hu6⟩ := point_tanh_6
  obtain ⟨hl7, hu7⟩ := point_tanh_7
  obtain ⟨hl8, hu8⟩ := point_tanh_8
  obtain ⟨hl9, hu9⟩ := point_tanh_9
  obtain ⟨hl10, hu10⟩ := point_tanh_10
  obtain ⟨hl11, hu11⟩ := point_tanh_11
  obtain ⟨hl12, hu12⟩ := point_tanh_12
  obtain ⟨hl13, hu13⟩ := point_tanh_13
  obtain ⟨hl14, hu14⟩ := point_tanh_14
  obtain ⟨hl15, hu15⟩ := point_tanh_15
  obtain ⟨hel, heu⟩ := point_exp
  norm_num [N, U, witness, p, certL] at *
  linarith

#check hpoint
#print axioms hpoint
end
end PoissonR3
