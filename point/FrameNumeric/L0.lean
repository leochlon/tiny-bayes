import FrameData.L0
import Layer0AttentionCheck
import Layer0OutputCheck
import WitnessAttentionCheck
import WitnessHiddenCheck
import WitnessOutputCheck
import PointChecks.L0.P0Q
import PointChecks.L0.P0A
import PointChecks.L0.P0H
import PointChecks.L0.P0O
import PointChecks.L0.P1Q
import PointChecks.L0.P1A
import PointChecks.L0.P1H
import PointChecks.L0.P1O
import PointChecks.L0.P2Q
import PointChecks.L0.P2A
import PointChecks.L0.P2H
import PointChecks.L0.P2O
import PointChecks.L0.P3Q
import PointChecks.L0.P3A
import PointChecks.L0.P3H
import PointChecks.L0.P3O
import PointChecks.L0.P4Q
import PointChecks.L0.P4A
import PointChecks.L0.P4H
import PointChecks.L0.P4O
import PointChecks.L0.P5Q
import PointChecks.L0.P5A
import PointChecks.L0.P5H
import PointChecks.L0.P5O
import PointChecks.L0.P6Q
import PointChecks.L0.P6A
import PointChecks.L0.P6H
import PointChecks.L0.P6O
import PointChecks.L0.P7Q
import PointChecks.L0.P7A
import PointChecks.L0.P7H
import PointChecks.L0.P7O
import PointChecks.L0.P8Q
import PointChecks.L0.P8A
import PointChecks.L0.P8H
import PointChecks.L0.P8O
import PointChecks.L0.P9Q
import PointChecks.L0.P9A
import PointChecks.L0.P9H
import PointChecks.L0.P9O
import PointChecks.L0.P10Q
import PointChecks.L0.P10A
import PointChecks.L0.P10H
import PointChecks.L0.P10O
import PointChecks.L0.P11Q
import PointChecks.L0.P11A
import PointChecks.L0.P11H
import PointChecks.L0.P11O
import PointChecks.L0.P12Q
import PointChecks.L0.P12A
import PointChecks.L0.P12H
import PointChecks.L0.P12O
import PointChecks.L0.P13Q
import PointChecks.L0.P13A
import PointChecks.L0.P13H
import PointChecks.L0.P13O
import PointChecks.L0.P14Q
import PointChecks.L0.P14A
import PointChecks.L0.P14H
import PointChecks.L0.P14O
import PointChecks.L0.P15Q
import PointChecks.L0.P15A
import PointChecks.L0.P15H
import PointChecks.L0.P15O
import PointChecks.L0.P16Q
import PointChecks.L0.P16A
import PointChecks.L0.P16H
import PointChecks.L0.P16O
import PointChecks.L0.P17Q
import PointChecks.L0.P17A
import PointChecks.L0.P17H
import PointChecks.L0.P17O
import PointChecks.L0.P18Q
import PointChecks.L0.P18A
import PointChecks.L0.P18H
import PointChecks.L0.P18O
import PointChecks.L0.P19Q
import PointChecks.L0.P19A
import PointChecks.L0.P19H
import PointChecks.L0.P19O
import PointChecks.L0.P20Q
import PointChecks.L0.P20A
import PointChecks.L0.P20H
import PointChecks.L0.P20O
import PointChecks.L0.P21Q
import PointChecks.L0.P21A
import PointChecks.L0.P21H
import PointChecks.L0.P21O
import PointChecks.L0.P22Q
import PointChecks.L0.P22A
import PointChecks.L0.P22H
import PointChecks.L0.P22O
import PointChecks.L0.P23Q
import PointChecks.L0.P23A
import PointChecks.L0.P23H
import PointChecks.L0.P23O
import PointChecks.L0.P24Q
import PointChecks.L0.P24A
import PointChecks.L0.P24H
import PointChecks.L0.P24O
import PointChecks.L0.P25Q
import PointChecks.L0.P25A
import PointChecks.L0.P25H
import PointChecks.L0.P25O
import PointChecks.L0.P26Q
import PointChecks.L0.P26A
import PointChecks.L0.P26H
import PointChecks.L0.P26O
import PointChecks.L0.P27Q
import PointChecks.L0.P27A
import PointChecks.L0.P27H
import PointChecks.L0.P27O
import PointChecks.L0.P28Q
import PointChecks.L0.P28A
import PointChecks.L0.P28H
import PointChecks.L0.P28O
import PointChecks.L0.P29Q
import PointChecks.L0.P29A
import PointChecks.L0.P29H
import PointChecks.L0.P29O
import PointChecks.L0.P30Q
import PointChecks.L0.P30A
import PointChecks.L0.P30H
import PointChecks.L0.P30O
import PointChecks.L0.P31Q
import PointChecks.L0.P31H
import PointChecks.L0.P32Q
namespace PythiaCert.Frame.L0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cq_checks : ∀ i, i < cx.length → PRO.qCheck (PRO.LL 0) (cx.getD i []) (cq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.q_check
  · exact Point.L0P1.q_check
  · exact Point.L0P2.q_check
  · exact Point.L0P3.q_check
  · exact Point.L0P4.q_check
  · exact Point.L0P5.q_check
  · exact Point.L0P6.q_check
  · exact Point.L0P7.q_check
  · exact Point.L0P8.q_check
  · exact Point.L0P9.q_check
  · exact Point.L0P10.q_check
  · exact Point.L0P11.q_check
  · exact Point.L0P12.q_check
  · exact Point.L0P13.q_check
  · exact Point.L0P14.q_check
  · exact Point.L0P15.q_check
  · exact Point.L0P16.q_check
  · exact Point.L0P17.q_check
  · exact Point.L0P18.q_check
  · exact Point.L0P19.q_check
  · exact Point.L0P20.q_check
  · exact Point.L0P21.q_check
  · exact Point.L0P22.q_check
  · exact Point.L0P23.q_check
  · exact Point.L0P24.q_check
  · exact Point.L0P25.q_check
  · exact Point.L0P26.q_check
  · exact Point.L0P27.q_check
  · exact Point.L0P28.q_check
  · exact Point.L0P29.q_check
  · exact Point.L0P30.q_check
  · exact Point.L0P31.q_check
theorem ca_checks : ∀ i, i < cx.length → PRO.aCheck (PRO.LL 0) i (cq.take (i+1)) (ca.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.a_check
  · exact Point.L0P1.a_check
  · exact Point.L0P2.a_check
  · exact Point.L0P3.a_check
  · exact Point.L0P4.a_check
  · exact Point.L0P5.a_check
  · exact Point.L0P6.a_check
  · exact Point.L0P7.a_check
  · exact Point.L0P8.a_check
  · exact Point.L0P9.a_check
  · exact Point.L0P10.a_check
  · exact Point.L0P11.a_check
  · exact Point.L0P12.a_check
  · exact Point.L0P13.a_check
  · exact Point.L0P14.a_check
  · exact Point.L0P15.a_check
  · exact Point.L0P16.a_check
  · exact Point.L0P17.a_check
  · exact Point.L0P18.a_check
  · exact Point.L0P19.a_check
  · exact Point.L0P20.a_check
  · exact Point.L0P21.a_check
  · exact Point.L0P22.a_check
  · exact Point.L0P23.a_check
  · exact Point.L0P24.a_check
  · exact Point.L0P25.a_check
  · exact Point.L0P26.a_check
  · exact Point.L0P27.a_check
  · exact Point.L0P28.a_check
  · exact Point.L0P29.a_check
  · exact Point.L0P30.a_check
  · exact layer0_31_attention_check
theorem ch_checks : ∀ i, i < cx.length → PRO.hCheck (PRO.LL 0) (cx.getD i []) (ch.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.h_check
  · exact Point.L0P1.h_check
  · exact Point.L0P2.h_check
  · exact Point.L0P3.h_check
  · exact Point.L0P4.h_check
  · exact Point.L0P5.h_check
  · exact Point.L0P6.h_check
  · exact Point.L0P7.h_check
  · exact Point.L0P8.h_check
  · exact Point.L0P9.h_check
  · exact Point.L0P10.h_check
  · exact Point.L0P11.h_check
  · exact Point.L0P12.h_check
  · exact Point.L0P13.h_check
  · exact Point.L0P14.h_check
  · exact Point.L0P15.h_check
  · exact Point.L0P16.h_check
  · exact Point.L0P17.h_check
  · exact Point.L0P18.h_check
  · exact Point.L0P19.h_check
  · exact Point.L0P20.h_check
  · exact Point.L0P21.h_check
  · exact Point.L0P22.h_check
  · exact Point.L0P23.h_check
  · exact Point.L0P24.h_check
  · exact Point.L0P25.h_check
  · exact Point.L0P26.h_check
  · exact Point.L0P27.h_check
  · exact Point.L0P28.h_check
  · exact Point.L0P29.h_check
  · exact Point.L0P30.h_check
  · exact Point.L0P31.h_check
theorem co_checks : ∀ i, i < cx.length → PRO.oCheck (PRO.LL 0) (cx.getD i []) (ca.getD i []) (ch.getD i []) (co.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.o_check
  · exact Point.L0P1.o_check
  · exact Point.L0P2.o_check
  · exact Point.L0P3.o_check
  · exact Point.L0P4.o_check
  · exact Point.L0P5.o_check
  · exact Point.L0P6.o_check
  · exact Point.L0P7.o_check
  · exact Point.L0P8.o_check
  · exact Point.L0P9.o_check
  · exact Point.L0P10.o_check
  · exact Point.L0P11.o_check
  · exact Point.L0P12.o_check
  · exact Point.L0P13.o_check
  · exact Point.L0P14.o_check
  · exact Point.L0P15.o_check
  · exact Point.L0P16.o_check
  · exact Point.L0P17.o_check
  · exact Point.L0P18.o_check
  · exact Point.L0P19.o_check
  · exact Point.L0P20.o_check
  · exact Point.L0P21.o_check
  · exact Point.L0P22.o_check
  · exact Point.L0P23.o_check
  · exact Point.L0P24.o_check
  · exact Point.L0P25.o_check
  · exact Point.L0P26.o_check
  · exact Point.L0P27.o_check
  · exact Point.L0P28.o_check
  · exact Point.L0P29.o_check
  · exact Point.L0P30.o_check
  · exact layer0_31_output_check
theorem wq_checks : ∀ i, i < wx.length → PRO.qCheck (PRO.LL 0) (wx.getD i []) (wq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.q_check
  · exact Point.L0P1.q_check
  · exact Point.L0P2.q_check
  · exact Point.L0P3.q_check
  · exact Point.L0P4.q_check
  · exact Point.L0P5.q_check
  · exact Point.L0P6.q_check
  · exact Point.L0P7.q_check
  · exact Point.L0P8.q_check
  · exact Point.L0P9.q_check
  · exact Point.L0P10.q_check
  · exact Point.L0P11.q_check
  · exact Point.L0P12.q_check
  · exact Point.L0P13.q_check
  · exact Point.L0P14.q_check
  · exact Point.L0P15.q_check
  · exact Point.L0P16.q_check
  · exact Point.L0P17.q_check
  · exact Point.L0P18.q_check
  · exact Point.L0P19.q_check
  · exact Point.L0P20.q_check
  · exact Point.L0P21.q_check
  · exact Point.L0P22.q_check
  · exact Point.L0P23.q_check
  · exact Point.L0P24.q_check
  · exact Point.L0P25.q_check
  · exact Point.L0P26.q_check
  · exact Point.L0P27.q_check
  · exact Point.L0P28.q_check
  · exact Point.L0P29.q_check
  · exact Point.L0P30.q_check
  · exact Point.L0P32.q_check
theorem wa_checks : ∀ i, i < wx.length → PRO.aCheck (PRO.LL 0) i (wq.take (i+1)) (wa.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.a_check
  · exact Point.L0P1.a_check
  · exact Point.L0P2.a_check
  · exact Point.L0P3.a_check
  · exact Point.L0P4.a_check
  · exact Point.L0P5.a_check
  · exact Point.L0P6.a_check
  · exact Point.L0P7.a_check
  · exact Point.L0P8.a_check
  · exact Point.L0P9.a_check
  · exact Point.L0P10.a_check
  · exact Point.L0P11.a_check
  · exact Point.L0P12.a_check
  · exact Point.L0P13.a_check
  · exact Point.L0P14.a_check
  · exact Point.L0P15.a_check
  · exact Point.L0P16.a_check
  · exact Point.L0P17.a_check
  · exact Point.L0P18.a_check
  · exact Point.L0P19.a_check
  · exact Point.L0P20.a_check
  · exact Point.L0P21.a_check
  · exact Point.L0P22.a_check
  · exact Point.L0P23.a_check
  · exact Point.L0P24.a_check
  · exact Point.L0P25.a_check
  · exact Point.L0P26.a_check
  · exact Point.L0P27.a_check
  · exact Point.L0P28.a_check
  · exact Point.L0P29.a_check
  · exact Point.L0P30.a_check
  · exact witness_attention_check
theorem wh_checks : ∀ i, i < wx.length → PRO.hCheck (PRO.LL 0) (wx.getD i []) (wh.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.h_check
  · exact Point.L0P1.h_check
  · exact Point.L0P2.h_check
  · exact Point.L0P3.h_check
  · exact Point.L0P4.h_check
  · exact Point.L0P5.h_check
  · exact Point.L0P6.h_check
  · exact Point.L0P7.h_check
  · exact Point.L0P8.h_check
  · exact Point.L0P9.h_check
  · exact Point.L0P10.h_check
  · exact Point.L0P11.h_check
  · exact Point.L0P12.h_check
  · exact Point.L0P13.h_check
  · exact Point.L0P14.h_check
  · exact Point.L0P15.h_check
  · exact Point.L0P16.h_check
  · exact Point.L0P17.h_check
  · exact Point.L0P18.h_check
  · exact Point.L0P19.h_check
  · exact Point.L0P20.h_check
  · exact Point.L0P21.h_check
  · exact Point.L0P22.h_check
  · exact Point.L0P23.h_check
  · exact Point.L0P24.h_check
  · exact Point.L0P25.h_check
  · exact Point.L0P26.h_check
  · exact Point.L0P27.h_check
  · exact Point.L0P28.h_check
  · exact Point.L0P29.h_check
  · exact Point.L0P30.h_check
  · exact witness_hidden_check
theorem wo_checks : ∀ i, i < wx.length → PRO.oCheck (PRO.LL 0) (wx.getD i []) (wa.getD i []) (wh.getD i []) (wo.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L0P0.o_check
  · exact Point.L0P1.o_check
  · exact Point.L0P2.o_check
  · exact Point.L0P3.o_check
  · exact Point.L0P4.o_check
  · exact Point.L0P5.o_check
  · exact Point.L0P6.o_check
  · exact Point.L0P7.o_check
  · exact Point.L0P8.o_check
  · exact Point.L0P9.o_check
  · exact Point.L0P10.o_check
  · exact Point.L0P11.o_check
  · exact Point.L0P12.o_check
  · exact Point.L0P13.o_check
  · exact Point.L0P14.o_check
  · exact Point.L0P15.o_check
  · exact Point.L0P16.o_check
  · exact Point.L0P17.o_check
  · exact Point.L0P18.o_check
  · exact Point.L0P19.o_check
  · exact Point.L0P20.o_check
  · exact Point.L0P21.o_check
  · exact Point.L0P22.o_check
  · exact Point.L0P23.o_check
  · exact Point.L0P24.o_check
  · exact Point.L0P25.o_check
  · exact Point.L0P26.o_check
  · exact Point.L0P27.o_check
  · exact Point.L0P28.o_check
  · exact Point.L0P29.o_check
  · exact Point.L0P30.o_check
  · exact witness_output_check
end PythiaCert.Frame.L0
