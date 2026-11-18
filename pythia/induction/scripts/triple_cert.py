"""Float64 check of `TripleCert` (pythia/induction/upper_bound/CON/Main.lean) against the full vocabulary.

The statements are read from Data.lean: one for each group c and positions i < j < l whose bit in
`freeMasks[c]` is clear (638,716 in all). Statement (a, b, c) says that for some order x, y, z of the
three tokens some token t != z has a logit at least that of z after the prompt [0, x, y, z, x, y].
For each statement and each of its six orders this script computes, in float64 over all 50,304 tokens,
the largest logit of a token t != z minus the logit of z; the statement holds in float64 when the
largest of these six values is >= 0.

Prints the number of groups and statements checked, the number that hold, the smallest best margin
over statements (how far below a competitor's logit the target lies, at least, in the most favourable
order), and the statements with the smallest best margins.

Usage (from the repository root):
  python3 pythia/induction/scripts/triple_cert.py [--model DIR] [--sample N] [--seed S] [--out FILE]
--model: a local copy of EleutherAI/pythia-14m; without it the model is downloaded from Hugging Face
at revision cf967c0a9a04383db6f7b1108d86b2962634b4ac. --sample: check a uniform random sample of N
statements instead of all of them. --out: write [a, b, c, x, y, z, competitor, best margin] for every
checked statement as JSON.
"""
import argparse, itertools, json, re, time
from pathlib import Path

import numpy as np
import torch
from transformers import GPTNeoXForCausalLM

ROOT = Path(__file__).resolve().parents[2]
REPO, REVISION = "EleutherAI/pythia-14m", "cf967c0a9a04383db6f7b1108d86b2962634b4ac"


def load_model(path):
    kw = {"local_files_only": True} if path else {"revision": REVISION}
    return GPTNeoXForCausalLM.from_pretrained(path or REPO, **kw).to(torch.float64).eval()


def statements():
    t = (ROOT / "induction/upper_bound/CON/Data.lean").read_text()
    groups = []
    for k in itertools.count():
        m = re.search(r"def groups%d : List \(List Nat\) := \[(.*?)\]\]\n" % k, t, re.S)
        if not m:
            break
        groups += [[int(x) for x in g.split(",")] for g in re.findall(r"\[([^\[\]]*)\]", m.group(1) + "]")]
    masks = [int(x, 16) for x in re.search(r"def freeMasks : List Nat := \[(.*?)\]", t, re.S).group(1).split(",")]
    out = []
    for g, mask in zip(groups, masks):
        for i, j, l in itertools.combinations(range(len(g)), 3):
            if not (mask >> (l * (l - 1) * (l - 2) // 6 + j * (j - 1) // 2 + i)) & 1:
                out.append((g[i], g[j], g[l]))
    return len(groups), np.array(out, dtype=np.int64)


def best_competitor(model, R, B=4096):
    """Largest logit of t != z minus logit of z, and that t, for rows (x, y, z) of R."""
    W = model.embed_out.weight
    P = torch.tensor(np.concatenate([np.zeros((len(R), 1), dtype=np.int64), R, R[:, :2]], 1))
    marg, comp = [], []
    for b in range(0, len(R), B):
        Pb = P[b:b + B]
        lg = model.gpt_neox(Pb).last_hidden_state[:, 5, :] @ W.T
        z = Pb[:, 3:4]
        tl = lg.gather(1, z)[:, 0]
        lg.scatter_(1, z, -torch.inf)
        mx, am = lg.max(1)
        marg.append((mx - tl).numpy())
        comp.append(am.numpy())
    return np.concatenate(marg), np.concatenate(comp)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model")
    ap.add_argument("--sample", type=int)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out")
    a = ap.parse_args()
    torch.set_grad_enabled(False)
    t0 = time.time()
    ngroups, S = statements()
    print("groups %d, statements of TripleCert %d" % (ngroups, len(S)), flush=True)
    if a.sample:
        S = S[np.sort(np.random.default_rng(a.seed).choice(len(S), a.sample, replace=False))]
        print("checking a uniform random sample of %d statements (seed %d)" % (len(S), a.seed), flush=True)
    model = load_model(a.model)
    perms = list(itertools.permutations(range(3)))
    R = S[:, perms].reshape(-1, 3)
    marg, comp = best_competitor(model, R)
    marg, comp = marg.reshape(-1, 6), comp.reshape(-1, 6)
    k = marg.argmax(1)
    best = marg[np.arange(len(S)), k]
    order = R.reshape(-1, 6, 3)[np.arange(len(S)), k]
    winner = comp[np.arange(len(S)), k]
    print("statements checked %d, holding in float64 (some order with a competitor >= target) %d (%.0f s)"
          % (len(S), int((best >= 0).sum()), time.time() - t0))
    print("smallest best margin (competitor logit minus target logit): %.6f" % float(best.min()))
    for i in np.argsort(best)[:10]:
        print("  tokens %s: order %s, competitor %d, margin %.6f" % (S[i].tolist(), order[i].tolist(), winner[i], best[i]))
    if a.out:
        json.dump([[*map(int, s), *map(int, o), int(w), float(m)] for s, o, w, m in zip(S, order, winner, best)],
                  open(a.out, "w"))


if __name__ == "__main__":
    main()
