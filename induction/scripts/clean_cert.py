"""Float64 check of `CleanCert` (induction/lower_bound/PRO/Main.lean).

For every list r of m distinct tokens of `cleanSet` with 3 <= m <= 8 (623,448 lists) and every k with
2 <= k <= m - 1, the prompt is [0] + r + r[:k] and the margin is the logit of r[k] (0-based, the
token after the second r_k) minus the largest logit of the other 50,303 tokens at the last position.
`CleanCert` says every margin is positive.

Prints, for each m, the number of lists, the number of lists with some margin <= 0 and the smallest
margin; then the totals and the list and k with the smallest margin.

Usage (from the release folder): python3 induction/scripts/clean_cert.py [--model DIR] [--batch B]
--model: a local copy of EleutherAI/pythia-14m; without it the model is downloaded from Hugging Face
at revision cf967c0a9a04383db6f7b1108d86b2962634b4ac.
"""
import argparse, itertools, re, time
from pathlib import Path

import torch
from transformers import GPTNeoXForCausalLM

ROOT = Path(__file__).resolve().parents[2]
REPO, REVISION = "EleutherAI/pythia-14m", "cf967c0a9a04383db6f7b1108d86b2962634b4ac"


def load_model(path):
    kw = {"local_files_only": True} if path else {"revision": REVISION}
    return GPTNeoXForCausalLM.from_pretrained(path or REPO, **kw).to(torch.float64).eval()


def clean_set():
    src = (ROOT / "induction/lower_bound/PRO/Main.lean").read_text()
    return [int(t) for t in re.search(r"def cleanSet : Finset ℕ := \{([^}]*)\}", src).group(1).split(",")]


def margins(model, r, k_lo, B):
    """Margins of the lists in r (shape N x m) for k = k_lo .. m-1, shape N x (m - k_lo)."""
    W = model.embed_out.weight
    N, m = r.shape
    out = []
    for b in range(0, N, B):
        rb = r[b:b + B]
        seq = torch.cat([torch.zeros(len(rb), 1, dtype=torch.long), rb, rb], 1)
        h = model.gpt_neox(seq).last_hidden_state
        cols = []
        for k in range(k_lo, m):
            lg = h[:, m + k, :] @ W.T
            tgt = rb[:, k]
            tl = lg.gather(1, tgt[:, None])[:, 0]
            lg.scatter_(1, tgt[:, None], -torch.inf)
            cols.append(tl - lg.max(1).values)
        out.append(torch.stack(cols, 1))
    return torch.cat(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model")
    ap.add_argument("--batch", type=int, default=1000)
    a = ap.parse_args()
    torch.set_grad_enabled(False)
    model = load_model(a.model)
    toks = clean_set()
    T = torch.tensor(toks)
    print("cleanSet:", toks, flush=True)
    t0 = time.time()
    lists = cases = bad = 0
    worst = (float("inf"), None, None)
    for m in range(3, 9):
        idx = torch.tensor(list(itertools.permutations(range(len(toks)), m)))
        r = T[idx]
        mg = margins(model, r, 2, a.batch)
        nbad = int((mg <= 0).any(1).sum())
        v, i = mg.min(1)
        j = int(v.argmin())
        if float(v[j]) < worst[0]:
            worst = (float(v[j]), r[j].tolist(), 2 + int(i[j]))
        lists += len(r); cases += mg.numel(); bad += nbad
        print("m=%d: lists %d, cases %d, lists with a margin <= 0: %d, smallest margin %.6f  (%.0f s)"
              % (m, len(r), mg.numel(), nbad, float(v[j]), time.time() - t0), flush=True)
    print("total: lists %d, cases %d, lists with a margin <= 0: %d" % (lists, cases, bad))
    print("smallest margin %.6f at r = %s, k = %d" % worst)


if __name__ == "__main__":
    main()
