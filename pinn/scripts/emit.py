"""Write a certificate from partition.py as the Lean modules PINN/ChkN, PINN/ChkH, PINN/DataN.lean and
PINN/DataH.lean. Run from pinn/: python3 scripts/emit.py cert.json [output root, default PINN]"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mirror as m

cert = json.load(open(sys.argv[1]))
PER = 6
ROOT = sys.argv[2] if len(sys.argv) > 2 else "PINN"
SPEC = {"N": ("ChkN", "okRN", "certN", 2, "gN0", "data/net.json"),
        "H": ("ChkH", "okRH", "certH", 3, "zero", "data/net_hardic.json")}

for name, (dirn, okf, cname, num, g0, path) in SPEC.items():
    L = [tuple(x) for x in cert[name]]
    P = m.load(path)
    assert m.chainOK(0, L)
    G0 = m.add(m.one, m.neg(m.netAll(P, m.tI(0, 0), False)[0])) if name == "N" else m.zero
    assert m.seqOK(num, G0, G0, m.one, L)
    os.makedirs(f"{ROOT}/{dirn}", exist_ok=True)
    chunks = [L[i:i + PER] for i in range(0, len(L), PER)]
    mods = []
    for ci, ch in enumerate(chunks):
        mod = f"C{ci:03d}"
        mods.append(mod)
        body = ",\n  ".join(f"({a}, {b}, {lo}, {hi})" for a, b, lo, hi in ch)
        thms = "".join(f"set_option maxHeartbeats 0 in\ntheorem ok{i} : PINN.{okf} ({a}, {b}, {lo}, {hi}) = true := by\n  decide +kernel\n\n" for i, (a, b, lo, hi) in enumerate(ch))
        names = ", ".join(f"ok{i}" for i in range(len(ch)))
        with open(f"{ROOT}/{dirn}/{mod}.lean", "w") as f:
            f.write(f"import PINN.Interval\n\n/-! Pieces {ci * PER}..{ci * PER + len(ch) - 1} of the certificate for "
                    f"`{'N' if name == 'N' else 'û'}`, kernel-checked. -/\n\n"
                    f"namespace PINN.{dirn}.{mod}\n\n/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/\n"
                    f"def L : List PINN.Piece := [\n  {body}]\n\n"
                    f"{thms}theorem ok : L.all PINN.{okf} = true := by\n  simp only [L, List.all_cons, List.all_nil, {names}, Bool.and_self, Bool.and_true]\n\n"
                    f"end PINN.{dirn}.{mod}\n")
    imports = "\n".join(f"import PINN.{dirn}.{mod}" for mod in mods)
    app = " ++\n    ".join(f"{dirn}.{mod}.L" for mod in mods)
    oks = ", ".join(f"{dirn}.{mod}.ok" for mod in mods)
    data = "Data" + name
    with open(f"{ROOT}/{data}.lean", "w") as f:
        f.write(f"{imports}\n\n/-! The certificate for `{'N' if name == 'N' else 'û'}`: {len(L)} pieces, "
                f"{len(chunks)} kernel-checked chunks. -/\n\nnamespace PINN\n\n"
                f"/-- All pieces, in order. -/\ndef {cname} : List Piece :=\n    {app}\n\n"
                f"theorem {cname}_all : {cname}.all {okf} = true := by\n"
                f"  simp only [{cname}, List.all_append, {oks}, Bool.and_self]\n\n"
                f"set_option maxHeartbeats 0 in\ntheorem {cname}_chain : chainOK 0 {cname} = true := by\n  decide +kernel\n\n"
                f"set_option maxHeartbeats 0 in\ntheorem {cname}_seq : seqOK {num} {g0} {g0} one {cname} = true := by\n"
                f"  decide +kernel\n\nend PINN\n")
    print(name, len(L), "pieces", len(chunks), "chunks")
