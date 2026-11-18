import OutputDefs
import PointData.L5.P31
import PointData.L5.P32

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem center_final_check : PRO.allSub
    (PRO.layerNormI CON.W.lnfg CON.W.lnfb Point.L5P31.o) Output.center = true := by
  decide +kernel

theorem witness_final_check : PRO.allSub
    (PRO.layerNormI CON.W.lnfg CON.W.lnfb Point.L5P32.o) Output.witness = true := by
  decide +kernel

theorem center_norm_sound {h : List ℝ}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h Point.L5P31.o) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.layerNorm CON.pythia14m.lnfg CON.pythia14m.lnfb h) Output.center := by
  have hlen : h.length = 128 := hh.length_eq.trans (by decide +kernel)
  exact f2_sub (layerNorm_sound CON.W.lnfg CON.W.lnfb hlen hh) _ center_final_check

theorem witness_norm_sound {h : List ℝ}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h Point.L5P32.o) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.layerNorm CON.pythia14m.lnfg CON.pythia14m.lnfb h) Output.witness := by
  have hlen : h.length = 128 := hh.length_eq.trans (by decide +kernel)
  exact f2_sub (layerNorm_sound CON.W.lnfg CON.W.lnfb hlen hh) _ witness_final_check

#print axioms center_final_check
#print axioms witness_final_check
#print axioms center_norm_sound
#print axioms witness_norm_sound
end PythiaCert
