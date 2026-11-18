"""Exact semantics of both networks (mpmath, 50 significant digits).

    z1_i(t) = W1[i] t + b1[i];  z2_j(t) = sum_i W2[j][i] tanh(z1_i(t)) + b2[j];  N(t) = sum_j W3[j] tanh(z2_j(t)) + b3
    N'(t)   = sum_j W3[j] (1 - tanh(z2_j)^2) sum_i W2[j][i] (1 - tanh(z1_i)^2) W1[i]
net.json:        the model is N itself.
net_hardic.json: the model is u(t) = 1 + t N(t), so u(0) = 1 exactly and u'(t) = N(t) + t N'(t).
residual r(t) = model'(t) + model(t) - exp(-t);  true solution (1 + t) exp(-t).
Every weight is the integer in the json file divided by its "denominator".
Usage: python3 reference.py <net.json | net_hardic.json> [t ...]
"""
import json, sys
from mpmath import mp, mpf, tanh, exp

mp.dps = 50


def load(path):
    net = json.load(open(path)); D = mpf(net["denominator"])
    p = ([mpf(w) / D for w in net["W1"]], [mpf(w) / D for w in net["b1"]],
         [[mpf(w) / D for w in row] for row in net["W2"]], [mpf(w) / D for w in net["b2"]],
         [mpf(w) / D for w in net["W3"]], mpf(net["b3"]) / D)
    return p, "1 + t" in net["definition"]


def N_dN(p, t):
    W1, b1, W2, b2, W3, b3 = p
    t = mpf(t)
    a1 = [tanh(w * t + b) for w, b in zip(W1, b1)]
    d1 = [(1 - a * a) * w for a, w in zip(a1, W1)]
    N, dN = b3, mpf(0)
    for row, b, c in zip(W2, b2, W3):
        a2 = tanh(sum(w * a for w, a in zip(row, a1)) + b)
        N += c * a2
        dN += c * (1 - a2 * a2) * sum(w * d for w, d in zip(row, d1))
    return N, dN


def model(p, hard, t):
    """(u(t), u'(t)) of the model."""
    N, dN = N_dN(p, t)
    t = mpf(t)
    return (1 + t * N, N + t * dN) if hard else (N, dN)


def residual(p, hard, t):
    u, du = model(p, hard, t)
    return du + u - exp(-mpf(t))


def solution(t):
    t = mpf(t)
    return (1 + t) * exp(-t)


if __name__ == "__main__":
    path = sys.argv[1]
    p, hard = load(path)
    for t in sys.argv[2:] or ["0", "1", "2", "3", "4"]:
        u, du = model(p, hard, t)
        print(f"t={t}: model={mp.nstr(u, 20)}  model'={mp.nstr(du, 20)}  residual={mp.nstr(du + u - exp(-mpf(t)), 12)}  "
              f"u*-model={mp.nstr(solution(t) - u, 12)}")
