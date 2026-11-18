import StagedExpr
import CellEnvelope
namespace PinnStaged
open PinnCert
def check (b : Cell) : Bool :=
  Cell.secondEnvelopeCheck b 4831208875216605
    (out0.interval (cst b.cx) (cst b.cy))
    (out1.interval (cst b.cx) (cst b.cy))
    (out2.interval (cst b.cx) (cst b.cy))
    (out3.interval b.X b.Y) (out4.interval b.X b.Y)
    (out5.interval b.X b.Y) (out6.interval b.X b.Y)
end PinnStaged
