import FrameData.L4
import PointChecks.L4.P0Q
import PointChecks.L4.P0A
import PointChecks.L4.P0H
import PointChecks.L4.P0O
import PointChecks.L4.P1Q
import PointChecks.L4.P1A
import PointChecks.L4.P1H
import PointChecks.L4.P1O
import PointChecks.L4.P2Q
import PointChecks.L4.P2A
import PointChecks.L4.P2H
import PointChecks.L4.P2O
import PointChecks.L4.P3Q
import PointChecks.L4.P3A
import PointChecks.L4.P3H
import PointChecks.L4.P3O
import PointChecks.L4.P4Q
import PointChecks.L4.P4A
import PointChecks.L4.P4H
import PointChecks.L4.P4O
import PointChecks.L4.P5Q
import PointChecks.L4.P5A
import PointChecks.L4.P5H
import PointChecks.L4.P5O
import PointChecks.L4.P6Q
import PointChecks.L4.P6A
import PointChecks.L4.P6H
import PointChecks.L4.P6O
import PointChecks.L4.P7Q
import PointChecks.L4.P7A
import PointChecks.L4.P7H
import PointChecks.L4.P7O
import PointChecks.L4.P8Q
import PointChecks.L4.P8A
import PointChecks.L4.P8H
import PointChecks.L4.P8O
import PointChecks.L4.P9Q
import PointChecks.L4.P9A
import PointChecks.L4.P9H
import PointChecks.L4.P9O
import PointChecks.L4.P10Q
import PointChecks.L4.P10A
import PointChecks.L4.P10H
import PointChecks.L4.P10O
import PointChecks.L4.P11Q
import PointChecks.L4.P11A
import PointChecks.L4.P11H
import PointChecks.L4.P11O
import PointChecks.L4.P12Q
import PointChecks.L4.P12A
import PointChecks.L4.P12H
import PointChecks.L4.P12O
import PointChecks.L4.P13Q
import PointChecks.L4.P13A
import PointChecks.L4.P13H
import PointChecks.L4.P13O
import PointChecks.L4.P14Q
import PointChecks.L4.P14A
import PointChecks.L4.P14H
import PointChecks.L4.P14O
import PointChecks.L4.P15Q
import PointChecks.L4.P15A
import PointChecks.L4.P15H
import PointChecks.L4.P15O
import PointChecks.L4.P16Q
import PointChecks.L4.P16A
import PointChecks.L4.P16H
import PointChecks.L4.P16O
import PointChecks.L4.P17Q
import PointChecks.L4.P17A
import PointChecks.L4.P17H
import PointChecks.L4.P17O
import PointChecks.L4.P18Q
import PointChecks.L4.P18A
import PointChecks.L4.P18H
import PointChecks.L4.P18O
import PointChecks.L4.P19Q
import PointChecks.L4.P19A
import PointChecks.L4.P19H
import PointChecks.L4.P19O
import PointChecks.L4.P20Q
import PointChecks.L4.P20A
import PointChecks.L4.P20H
import PointChecks.L4.P20O
import PointChecks.L4.P21Q
import PointChecks.L4.P21A
import PointChecks.L4.P21H
import PointChecks.L4.P21O
import PointChecks.L4.P22Q
import PointChecks.L4.P22A
import PointChecks.L4.P22H
import PointChecks.L4.P22O
import PointChecks.L4.P23Q
import PointChecks.L4.P23A
import PointChecks.L4.P23H
import PointChecks.L4.P23O
import PointChecks.L4.P24Q
import PointChecks.L4.P24A
import PointChecks.L4.P24H
import PointChecks.L4.P24O
import PointChecks.L4.P25Q
import PointChecks.L4.P25A
import PointChecks.L4.P25H
import PointChecks.L4.P25O
import PointChecks.L4.P26Q
import PointChecks.L4.P26A
import PointChecks.L4.P26H
import PointChecks.L4.P26O
import PointChecks.L4.P27Q
import PointChecks.L4.P27A
import PointChecks.L4.P27H
import PointChecks.L4.P27O
import PointChecks.L4.P28Q
import PointChecks.L4.P28A
import PointChecks.L4.P28H
import PointChecks.L4.P28O
import PointChecks.L4.P29Q
import PointChecks.L4.P29A
import PointChecks.L4.P29H
import PointChecks.L4.P29O
import PointChecks.L4.P30Q
import PointChecks.L4.P30A
import PointChecks.L4.P30H
import PointChecks.L4.P30O
import PointChecks.L4.P31Q
import PointChecks.L4.P31A
import PointChecks.L4.P31H
import PointChecks.L4.P31O
import PointChecks.L4.P32Q
import PointChecks.L4.P32A
import PointChecks.L4.P32H
import PointChecks.L4.P32O
namespace PythiaCert.Frame.L4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cq_checks : ∀ i, i < cx.length → PRO.qCheck (PRO.LL 4) (cx.getD i []) (cq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.q_check
  · exact Point.L4P1.q_check
  · exact Point.L4P2.q_check
  · exact Point.L4P3.q_check
  · exact Point.L4P4.q_check
  · exact Point.L4P5.q_check
  · exact Point.L4P6.q_check
  · exact Point.L4P7.q_check
  · exact Point.L4P8.q_check
  · exact Point.L4P9.q_check
  · exact Point.L4P10.q_check
  · exact Point.L4P11.q_check
  · exact Point.L4P12.q_check
  · exact Point.L4P13.q_check
  · exact Point.L4P14.q_check
  · exact Point.L4P15.q_check
  · exact Point.L4P16.q_check
  · exact Point.L4P17.q_check
  · exact Point.L4P18.q_check
  · exact Point.L4P19.q_check
  · exact Point.L4P20.q_check
  · exact Point.L4P21.q_check
  · exact Point.L4P22.q_check
  · exact Point.L4P23.q_check
  · exact Point.L4P24.q_check
  · exact Point.L4P25.q_check
  · exact Point.L4P26.q_check
  · exact Point.L4P27.q_check
  · exact Point.L4P28.q_check
  · exact Point.L4P29.q_check
  · exact Point.L4P30.q_check
  · exact Point.L4P31.q_check
theorem ca_checks : ∀ i, i < cx.length → PRO.aCheck (PRO.LL 4) i (cq.take (i+1)) (ca.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.a_check
  · exact Point.L4P1.a_check
  · exact Point.L4P2.a_check
  · exact Point.L4P3.a_check
  · exact Point.L4P4.a_check
  · exact Point.L4P5.a_check
  · exact Point.L4P6.a_check
  · exact Point.L4P7.a_check
  · exact Point.L4P8.a_check
  · exact Point.L4P9.a_check
  · exact Point.L4P10.a_check
  · exact Point.L4P11.a_check
  · exact Point.L4P12.a_check
  · exact Point.L4P13.a_check
  · exact Point.L4P14.a_check
  · exact Point.L4P15.a_check
  · exact Point.L4P16.a_check
  · exact Point.L4P17.a_check
  · exact Point.L4P18.a_check
  · exact Point.L4P19.a_check
  · exact Point.L4P20.a_check
  · exact Point.L4P21.a_check
  · exact Point.L4P22.a_check
  · exact Point.L4P23.a_check
  · exact Point.L4P24.a_check
  · exact Point.L4P25.a_check
  · exact Point.L4P26.a_check
  · exact Point.L4P27.a_check
  · exact Point.L4P28.a_check
  · exact Point.L4P29.a_check
  · exact Point.L4P30.a_check
  · exact Point.L4P31.a_check
theorem ch_checks : ∀ i, i < cx.length → PRO.hCheck (PRO.LL 4) (cx.getD i []) (ch.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.h_check
  · exact Point.L4P1.h_check
  · exact Point.L4P2.h_check
  · exact Point.L4P3.h_check
  · exact Point.L4P4.h_check
  · exact Point.L4P5.h_check
  · exact Point.L4P6.h_check
  · exact Point.L4P7.h_check
  · exact Point.L4P8.h_check
  · exact Point.L4P9.h_check
  · exact Point.L4P10.h_check
  · exact Point.L4P11.h_check
  · exact Point.L4P12.h_check
  · exact Point.L4P13.h_check
  · exact Point.L4P14.h_check
  · exact Point.L4P15.h_check
  · exact Point.L4P16.h_check
  · exact Point.L4P17.h_check
  · exact Point.L4P18.h_check
  · exact Point.L4P19.h_check
  · exact Point.L4P20.h_check
  · exact Point.L4P21.h_check
  · exact Point.L4P22.h_check
  · exact Point.L4P23.h_check
  · exact Point.L4P24.h_check
  · exact Point.L4P25.h_check
  · exact Point.L4P26.h_check
  · exact Point.L4P27.h_check
  · exact Point.L4P28.h_check
  · exact Point.L4P29.h_check
  · exact Point.L4P30.h_check
  · exact Point.L4P31.h_check
theorem co_checks : ∀ i, i < cx.length → PRO.oCheck (PRO.LL 4) (cx.getD i []) (ca.getD i []) (ch.getD i []) (co.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.o_check
  · exact Point.L4P1.o_check
  · exact Point.L4P2.o_check
  · exact Point.L4P3.o_check
  · exact Point.L4P4.o_check
  · exact Point.L4P5.o_check
  · exact Point.L4P6.o_check
  · exact Point.L4P7.o_check
  · exact Point.L4P8.o_check
  · exact Point.L4P9.o_check
  · exact Point.L4P10.o_check
  · exact Point.L4P11.o_check
  · exact Point.L4P12.o_check
  · exact Point.L4P13.o_check
  · exact Point.L4P14.o_check
  · exact Point.L4P15.o_check
  · exact Point.L4P16.o_check
  · exact Point.L4P17.o_check
  · exact Point.L4P18.o_check
  · exact Point.L4P19.o_check
  · exact Point.L4P20.o_check
  · exact Point.L4P21.o_check
  · exact Point.L4P22.o_check
  · exact Point.L4P23.o_check
  · exact Point.L4P24.o_check
  · exact Point.L4P25.o_check
  · exact Point.L4P26.o_check
  · exact Point.L4P27.o_check
  · exact Point.L4P28.o_check
  · exact Point.L4P29.o_check
  · exact Point.L4P30.o_check
  · exact Point.L4P31.o_check
theorem wq_checks : ∀ i, i < wx.length → PRO.qCheck (PRO.LL 4) (wx.getD i []) (wq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.q_check
  · exact Point.L4P1.q_check
  · exact Point.L4P2.q_check
  · exact Point.L4P3.q_check
  · exact Point.L4P4.q_check
  · exact Point.L4P5.q_check
  · exact Point.L4P6.q_check
  · exact Point.L4P7.q_check
  · exact Point.L4P8.q_check
  · exact Point.L4P9.q_check
  · exact Point.L4P10.q_check
  · exact Point.L4P11.q_check
  · exact Point.L4P12.q_check
  · exact Point.L4P13.q_check
  · exact Point.L4P14.q_check
  · exact Point.L4P15.q_check
  · exact Point.L4P16.q_check
  · exact Point.L4P17.q_check
  · exact Point.L4P18.q_check
  · exact Point.L4P19.q_check
  · exact Point.L4P20.q_check
  · exact Point.L4P21.q_check
  · exact Point.L4P22.q_check
  · exact Point.L4P23.q_check
  · exact Point.L4P24.q_check
  · exact Point.L4P25.q_check
  · exact Point.L4P26.q_check
  · exact Point.L4P27.q_check
  · exact Point.L4P28.q_check
  · exact Point.L4P29.q_check
  · exact Point.L4P30.q_check
  · exact Point.L4P32.q_check
theorem wa_checks : ∀ i, i < wx.length → PRO.aCheck (PRO.LL 4) i (wq.take (i+1)) (wa.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.a_check
  · exact Point.L4P1.a_check
  · exact Point.L4P2.a_check
  · exact Point.L4P3.a_check
  · exact Point.L4P4.a_check
  · exact Point.L4P5.a_check
  · exact Point.L4P6.a_check
  · exact Point.L4P7.a_check
  · exact Point.L4P8.a_check
  · exact Point.L4P9.a_check
  · exact Point.L4P10.a_check
  · exact Point.L4P11.a_check
  · exact Point.L4P12.a_check
  · exact Point.L4P13.a_check
  · exact Point.L4P14.a_check
  · exact Point.L4P15.a_check
  · exact Point.L4P16.a_check
  · exact Point.L4P17.a_check
  · exact Point.L4P18.a_check
  · exact Point.L4P19.a_check
  · exact Point.L4P20.a_check
  · exact Point.L4P21.a_check
  · exact Point.L4P22.a_check
  · exact Point.L4P23.a_check
  · exact Point.L4P24.a_check
  · exact Point.L4P25.a_check
  · exact Point.L4P26.a_check
  · exact Point.L4P27.a_check
  · exact Point.L4P28.a_check
  · exact Point.L4P29.a_check
  · exact Point.L4P30.a_check
  · exact Point.L4P32.a_check
theorem wh_checks : ∀ i, i < wx.length → PRO.hCheck (PRO.LL 4) (wx.getD i []) (wh.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.h_check
  · exact Point.L4P1.h_check
  · exact Point.L4P2.h_check
  · exact Point.L4P3.h_check
  · exact Point.L4P4.h_check
  · exact Point.L4P5.h_check
  · exact Point.L4P6.h_check
  · exact Point.L4P7.h_check
  · exact Point.L4P8.h_check
  · exact Point.L4P9.h_check
  · exact Point.L4P10.h_check
  · exact Point.L4P11.h_check
  · exact Point.L4P12.h_check
  · exact Point.L4P13.h_check
  · exact Point.L4P14.h_check
  · exact Point.L4P15.h_check
  · exact Point.L4P16.h_check
  · exact Point.L4P17.h_check
  · exact Point.L4P18.h_check
  · exact Point.L4P19.h_check
  · exact Point.L4P20.h_check
  · exact Point.L4P21.h_check
  · exact Point.L4P22.h_check
  · exact Point.L4P23.h_check
  · exact Point.L4P24.h_check
  · exact Point.L4P25.h_check
  · exact Point.L4P26.h_check
  · exact Point.L4P27.h_check
  · exact Point.L4P28.h_check
  · exact Point.L4P29.h_check
  · exact Point.L4P30.h_check
  · exact Point.L4P32.h_check
theorem wo_checks : ∀ i, i < wx.length → PRO.oCheck (PRO.LL 4) (wx.getD i []) (wa.getD i []) (wh.getD i []) (wo.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L4P0.o_check
  · exact Point.L4P1.o_check
  · exact Point.L4P2.o_check
  · exact Point.L4P3.o_check
  · exact Point.L4P4.o_check
  · exact Point.L4P5.o_check
  · exact Point.L4P6.o_check
  · exact Point.L4P7.o_check
  · exact Point.L4P8.o_check
  · exact Point.L4P9.o_check
  · exact Point.L4P10.o_check
  · exact Point.L4P11.o_check
  · exact Point.L4P12.o_check
  · exact Point.L4P13.o_check
  · exact Point.L4P14.o_check
  · exact Point.L4P15.o_check
  · exact Point.L4P16.o_check
  · exact Point.L4P17.o_check
  · exact Point.L4P18.o_check
  · exact Point.L4P19.o_check
  · exact Point.L4P20.o_check
  · exact Point.L4P21.o_check
  · exact Point.L4P22.o_check
  · exact Point.L4P23.o_check
  · exact Point.L4P24.o_check
  · exact Point.L4P25.o_check
  · exact Point.L4P26.o_check
  · exact Point.L4P27.o_check
  · exact Point.L4P28.o_check
  · exact Point.L4P29.o_check
  · exact Point.L4P30.o_check
  · exact Point.L4P32.o_check
end PythiaCert.Frame.L4
