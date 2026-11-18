"""Order averages of Pythia-14M on the red/blue encoding: the table `tbl` of pythia/interval/PRO/Claim.lean.

For every binary sequence x with |x| <= 8 the prompt is <|endoftext|> (id 0) followed by " red,"
(ids 2502, 13) for each 1 and " blue," (ids 4797, 13) for each 0, and
p(x) = P(" red") / (P(" red") + P(" blue")) at the last position, evaluated in float64.
For each of the 45 bags (n, k) with n <= 8 the order average of p over the C(n, k) orderings is
rounded to ten-thousandths.

Prints the table in the layout of `tbl`, whether it equals `tbl` in Claim.lean, the smallest distance
of an average from a rounding boundary, each average's deviation from Laplace's rule (k+1)/(n+2)
(the orange points of Figure 2), the largest deviations from Laplace's rule and from the Beta(2, 9/4)
predictive (4k+8)/(4n+17), and the order gap p(00001111) - p(11110000) of `Numerics8`.

Usage (from the repository root): python3 pythia/interval/scripts/red_blue_table.py [--model DIR] [--out FILE]
--model: a local copy of EleutherAI/pythia-14m; without it the model is downloaded from Hugging Face
at revision cf967c0a9a04383db6f7b1108d86b2962634b4ac. --out: write p(x) for all 511 sequences as JSON.
"""
import argparse, ast, itertools, json, math, re
from pathlib import Path

import torch
from transformers import GPTNeoXForCausalLM

ROOT = Path(__file__).resolve().parents[2]
REPO, REVISION = "EleutherAI/pythia-14m", "cf967c0a9a04383db6f7b1108d86b2962634b4ac"
BOS, RED, BLUE, COMMA = 0, 2502, 4797, 13
N = 8


def load_model(path):
    kw = {"local_files_only": True} if path else {"revision": REVISION}
    return GPTNeoXForCausalLM.from_pretrained(path or REPO, **kw).to(torch.float64).eval()


def lean_table():
    src = (ROOT / "interval/PRO/Claim.lean").read_text()
    body = re.search(r"def tbl : List \(List ℤ\) :=\s*(\[.*?\]\])", src, re.S).group(1)
    return ast.literal_eval(body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model")
    ap.add_argument("--out")
    a = ap.parse_args()
    torch.set_grad_enabled(False)
    model = load_model(a.model)

    p = {}
    for n in range(N + 1):
        xs = list(itertools.product((0, 1), repeat=n))
        ids = [[BOS] + [t for b in x for t in ((RED if b else BLUE), COMMA)] for x in xs]
        lg = model(torch.tensor(ids)).logits[:, -1, :]
        d = (lg[:, RED] - lg[:, BLUE]).tolist()
        for x, v in zip(xs, d):
            p[x] = 1 / (1 + math.exp(-v))

    avg = {}
    for n in range(N + 1):
        for k in range(n + 1):
            vals = [v for x, v in p.items() if len(x) == n and sum(x) == k]
            avg[n, k] = sum(vals) / len(vals)
    tbl = [[round(avg[n, k] * 10000) for k in range(n + 1)] for n in range(N + 1)]

    print("order averages in ten-thousandths:")
    print("[" + ",\n ".join("[" + ", ".join(map(str, row)) + "]" for row in tbl) + "]")
    ref = lean_table()
    diff = [(n, k, tbl[n][k], ref[n][k]) for n in range(N + 1) for k in range(n + 1) if tbl[n][k] != ref[n][k]]
    print("entries equal to tbl in interval/PRO/Claim.lean: %d of 45" % (45 - len(diff)))
    for n, k, c, r in diff:
        print("  differs at (%d, %d): computed %d, tbl %d" % (n, k, c, r))
    edge = min(abs(avg[nk] * 10000 - math.floor(avg[nk] * 10000) - 0.5) for nk in avg)
    print("smallest distance of an average from a rounding boundary: %.3e ten-thousandths" % edge)

    print("deviation from Laplace's rule, avg(n, k) - (k+1)/(n+2):")
    for n in range(N + 1):
        print("  n=%d: %s" % (n, " ".join("%+.4f" % (avg[n, k] - (k + 1) / (n + 2)) for k in range(n + 1))))
    lap = max(abs(avg[n, k] - (k + 1) / (n + 2)) for n, k in avg)
    beta = max(abs(avg[n, k] - (4 * k + 8) / (4 * n + 17)) for n, k in avg)
    print("largest |avg - Laplace|: %.4f; largest |avg - Beta(2, 9/4)|: %.4f" % (lap, beta))
    gap = p[(0, 0, 0, 0, 1, 1, 1, 1)] - p[(1, 1, 1, 1, 0, 0, 0, 0)]
    print("order gap p(00001111) - p(11110000): %.6f" % gap)
    print("p(empty): %.10f" % p[()])

    if a.out:
        json.dump({"".join(map(str, x)): v for x, v in p.items()}, open(a.out, "w"))


if __name__ == "__main__":
    main()
