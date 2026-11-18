import OracleInterval
import CellEnvelope
namespace PinnOracle
open PinnCert
def envelope (b : Cell) (c d : Oracle) : Bool :=
  Cell.secondEnvelopeCheck b 4831208875216605
    (iv0 c (cst b.cx) (cst b.cy))
    (iv1 c (cst b.cx) (cst b.cy))
    (iv2 c (cst b.cx) (cst b.cy))
    (iv3 d b.X b.Y) (iv4 d b.X b.Y) (iv5 d b.X b.Y) (iv6 d b.X b.Y)
end PinnOracle
