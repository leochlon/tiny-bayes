"""Partition [0, 4] by binary search for the longest pieces whose residual enclosure has width <= delta, then
check the bounds at every partition point. Run from pinn/ode/: python3 scripts/partition.py 9e-5 1.1e-4 cert.json"""
import json, os, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mirror as m

NETS = {"N": ("data/net.json", m.rNI, m.rdNI, 2), "H": ("data/net_hardic.json", m.rHI, m.rdHI, 3)}
DEL = {"N": float(sys.argv[1]), "H": float(sys.argv[2])}
NSEG = 48
HMAX = 65536


def segment(args):
    name, lo_b, hi_b = args
    path, R, Rd, _ = NETS[name]
    P = m.load(path)
    dl = int(DEL[name] * m.S)
    def good(a, h):
        pb = m.piece_bounds(R, Rd, P, a, a + h)
        return pb is not None and pb[1] - pb[0] <= dl
    out = []; a = lo_b
    while a < hi_b:
        top = min(HMAX, hi_b - a)
        if good(a, top):
            h = top
        else:
            lo, hi = 1, top
            while hi - lo > max(1, lo // 64):
                mid = (lo + hi) // 2
                if good(a, mid): lo = mid
                else: hi = mid
            h = lo
        pb = m.piece_bounds(R, Rd, P, a, a + h)
        assert pb[1] - pb[0] <= dl
        out.append((a, a + h, pb[0], pb[1]))
        a += h
    return out


if __name__ == "__main__":
    t0 = time.time()
    res = {}
    with Pool(48) as pool:
        for name in NETS:
            bnds = [i * 4194304 // NSEG for i in range(NSEG + 1)]
            parts = pool.map(segment, [(name, bnds[i], bnds[i + 1]) for i in range(NSEG)])
            res[name] = [x for p in parts for x in p]
            print(name, "pieces", len(res[name]), "time", round(time.time() - t0, 1), flush=True)
    for name in NETS:
        L = res[name]; path, R, Rd, num = NETS[name]; P = m.load(path)
        assert m.chainOK(0, L)
        G0 = m.add(m.one, m.neg(m.netAll(P, m.tI(0, 0), False)[0])) if name == "N" else m.zero
        tr = []
        ok = m.seqOK(num, G0, G0, m.one, L, tr)
        print(name, "seqOK", ok, "max U at points", max(G[1] / E[0] for G, H, E in tr),
              "min L at points", min(H[0] / E[1] for G, H, E in tr), "pieces", len(L), flush=True)
        assert ok
    json.dump(res, open(sys.argv[3], "w"))
