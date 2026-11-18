"""The float32 search behind `freeMasks` (pythia/induction/upper_bound/CON/Data.lean), and a float64 recheck
of the failures it finds.

The token set V and its split into 167 groups are read from Data.lean. For every group and every
triple of positions i < j < l, each of the six orders x, y, z of the three tokens is run on the prompt
[0, x, y, z, x, y], and its margin is the logit of z minus the largest logit of the competitors: x, y
and a fixed candidate set, the tokens that were the top competitor of a target beaten by at least 0.1
on 30,000 random ordered triples of V (numpy seed 2), at most the 2,000 most frequent. The triple
fails when some order has margin <= -0.1 in float32; its bit in `freeMasks` is then clear, and the
order with the smallest margin and its competitor are its witness.
Each witness is then evaluated in float64 (target logit minus the named competitor's logit), which is
the evidence for the corresponding statement of `TripleCert`.

Prints the number of groups, triples and failing triples (= `TripleCert` statements), whether the
masks equal `freeMasks` in Data.lean (and how many bits differ), and the largest float64 witness
margin, i.e. how far below its competitor's logit every target is at least.

Usage (from the repository root):
  python3 pythia/induction/scripts/triple_search.py [--model DIR] [--witnesses FILE]
--model: a local copy of EleutherAI/pythia-14m; without it the model is downloaded from Hugging Face
at revision cf967c0a9a04383db6f7b1108d86b2962634b4ac. --witnesses: write the witnesses as JSON,
one [x, y, z, competitor, float32 margin, float64 margin] per failing triple.
"""
import argparse, itertools, json, re, time
from collections import Counter
from pathlib import Path

import numpy as np
import torch
from transformers import GPTNeoXForCausalLM

ROOT = Path(__file__).resolve().parents[2]
REPO, REVISION = "EleutherAI/pythia-14m", "cf967c0a9a04383db6f7b1108d86b2962634b4ac"
TAU = 0.1
SAMPLES, NCAND = 30000, 2000


def load_model(path, dtype):
    kw = {"local_files_only": True} if path else {"revision": REVISION}
    return GPTNeoXForCausalLM.from_pretrained(path or REPO, **kw).to(dtype).eval()


def lean_data():
    t = (ROOT / "induction/upper_bound/CON/Data.lean").read_text()
    V = []
    for k in itertools.count():
        m = re.search(r"def V%d : List Nat := \[(.*?)\]" % k, t)
        if not m:
            break
        V += [int(x) for x in m.group(1).split(",")]
    groups = []
    for k in itertools.count():
        m = re.search(r"def groups%d : List \(List Nat\) := \[(.*?)\]\]\n" % k, t, re.S)
        if not m:
            break
        groups += [[int(x) for x in g.split(",")] for g in re.findall(r"\[([^\[\]]*)\]", m.group(1) + "]")]
    masks = [int(x, 16) for x in re.search(r"def freeMasks : List Nat := \[(.*?)\]", t, re.S).group(1).split(",")]
    return V, groups, masks


def tidx(i, j, l):
    return l * (l - 1) * (l - 2) // 6 + j * (j - 1) // 2 + i


def candidates(model, V):
    rng = np.random.default_rng(2)
    W = model.embed_out.weight
    T = np.array(V)[np.stack([rng.permutation(len(V))[:3] for _ in range(SAMPLES)])]
    P = torch.tensor(np.stack([np.zeros(SAMPLES, dtype=np.int64), T[:, 0], T[:, 1], T[:, 2], T[:, 0], T[:, 1]], 1))
    cnt = Counter()
    for b in range(0, SAMPLES, 10000):
        lg = model.gpt_neox(P[b:b + 10000]).last_hidden_state[:, 5, :] @ W.T
        t = torch.tensor(T[b:b + 10000, 2])
        tl = lg.gather(1, t[:, None])[:, 0]
        lg.scatter_(1, t[:, None], -1e9)
        mx, am = lg.max(1)
        cnt.update(am[(tl - mx) <= -TAU].tolist())
    return torch.tensor([c for c, _ in cnt.most_common(NCAND)])


def search(model, R, cand, B=16384):
    """Float32 margin of z against the candidates and x, y, and the competitor, for rows (x, y, z) of R."""
    W = model.embed_out.weight
    WC = W[cand]
    P = torch.tensor(np.concatenate([np.zeros((len(R), 1), dtype=np.int64), R, R[:, :2]], 1))
    marg, comp = [], []
    for b in range(0, len(R), B):
        Pb = P[b:b + B]
        h = model.gpt_neox(Pb).last_hidden_state[:, 5, :]
        t = Pb[:, 3]
        tl = (h * W[t]).sum(1)
        lg = h @ WC.T
        lg[cand[None, :] == t[:, None]] = -1e9
        mx, am = lg.max(1)
        c = cand[am]
        for col in (1, 2):
            o = Pb[:, col]
            lo = (h * W[o]).sum(1)
            better = lo > mx
            mx = torch.where(better, lo, mx)
            c = torch.where(better, o, c)
        marg.append((tl - mx).numpy().astype(np.float64))
        comp.append(c.numpy())
    return np.concatenate(marg), np.concatenate(comp)


def recheck(model, R, comp, B=16384):
    """Float64 logit of z minus logit of the competitor on [0, x, y, z, x, y]."""
    W = model.embed_out.weight
    P = torch.tensor(np.concatenate([np.zeros((len(R), 1), dtype=np.int64), R, R[:, :2]], 1))
    C = torch.tensor(comp)
    out = []
    for b in range(0, len(R), B):
        h = model.gpt_neox(P[b:b + B]).last_hidden_state[:, 5, :]
        out.append(((h * W[P[b:b + B, 3]]).sum(1) - (h * W[C[b:b + B]]).sum(1)).numpy())
    return np.concatenate(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model")
    ap.add_argument("--witnesses")
    a = ap.parse_args()
    torch.set_grad_enabled(False)
    t0 = time.time()
    V, groups, lean_masks = lean_data()
    assert sorted(x for g in groups for x in g) == V and len(lean_masks) == len(groups)
    print("V: %d tokens; groups: %d of sizes %s" % (len(V), len(groups), sorted(Counter(map(len, groups)).items())), flush=True)

    m32 = load_model(a.model, torch.float32)
    cand = candidates(m32, V)
    print("candidate competitors: %d (%.0f s)" % (len(cand), time.time() - t0), flush=True)

    rows, owner = [], []
    for c, g in enumerate(groups):
        for tri in itertools.combinations(range(len(g)), 3):
            for o in itertools.permutations(tri):
                rows.append([g[i] for i in o])
            owner.append((c, tri))
    R = np.array(rows, dtype=np.int64)
    marg, comp = search(m32, R, cand)
    print("float32 search: %d triples, %d prompts (%.0f s)" % (len(owner), len(R), time.time() - t0), flush=True)

    marg = marg.reshape(-1, 6)
    best = marg.argmin(1)
    bm = marg[np.arange(len(owner)), best]
    fail = bm <= -TAU
    masks = [0] * len(groups)
    for (c, (i, j, l)), f in zip(owner, fail):
        if not f:
            masks[c] |= 1 << tidx(i, j, l)
    nd = sum(bin(x ^ y).count("1") for x, y in zip(masks, lean_masks))
    print("failing triples (clear bits, statements of TripleCert): %d of %d" % (int(fail.sum()), len(owner)))
    print("masks equal to freeMasks in Data.lean: %s (%d bits differ; %d groups differ)"
          % (masks == lean_masks, nd, sum(x != y for x, y in zip(masks, lean_masks))), flush=True)
    near = int((np.abs(bm + TAU) < 1e-3).sum())
    print("triples with a float32 margin within 1e-3 of -%.1f: %d" % (TAU, near), flush=True)

    sel = np.nonzero(fail)[0]
    wi = sel * 6 + best[sel]
    WR, WC = R[wi], comp.reshape(-1, 6)[sel, best[sel]]
    del m32
    m64 = load_model(a.model, torch.float64)
    m64v = recheck(m64, WR, WC)
    print("float64 recheck of %d witnesses: largest margin (target minus named competitor) %.6f, "
          "witnesses with margin >= 0: %d, max |float32 - float64| %.6f (%.0f s)"
          % (len(sel), float(m64v.max()), int((m64v >= 0).sum()), float(np.abs(m64v - bm[sel]).max()), time.time() - t0))

    if a.witnesses:
        json.dump([[*map(int, r), int(c), float(m), float(v)] for r, c, m, v in zip(WR, WC, bm[sel], m64v)],
                  open(a.witnesses, "w"))


if __name__ == "__main__":
    main()
