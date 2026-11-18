"""Exact Python mirror of PINN/Interval.lean (integer intervals at scale S = 2^64). The Lean kernel re-checks
everything it produces."""
import json

S = 2 ** 64; MQ = 32; TWO_M = 2 ** 32; SM = S * TWO_M
P48 = 2 ** 48; P44 = 2 ** 44


def fdiv(a, b): return a // b
def cdiv(a, b): return -((-a) // b)

zero = (0, 0, True); one = (S, S, True)
def cst(a): return (a, a, True)
def add(X, Y): return (X[0] + Y[0], X[1] + Y[1], X[2] and Y[2])
def neg(X): return (-X[1], -X[0], X[2])
def mulZ(w, X): return (w * X[0], w * X[1], X[2]) if w >= 0 else (w * X[1], w * X[0], X[2])
def mulRaw(X, Y):
    a, b, c, d = X[0] * Y[0], X[0] * Y[1], X[1] * Y[0], X[1] * Y[1]
    return (min(min(a, b), min(c, d)), max(max(a, b), max(c, d)), X[2] and Y[2])
def downBy(d, X): return (fdiv(X[0], d), cdiv(X[1], d), X[2])
def mul(X, Y): return downBy(S, mulRaw(X, Y))
def sqRaw(X):
    a, b = X[0] * X[0], X[1] * X[1]
    return (a if 0 <= X[0] else (b if X[1] <= 0 else 0), max(a, b), X[2])
def omsq(X): return add(one, neg(downBy(S, sqRaw(X))))
def sqLo(k, a):
    for _ in range(k): a = fdiv(a * a, S)
    return a
def sqHi(k, a):
    for _ in range(k): a = cdiv(a * a, S)
    return a
def expLo(n): return sqLo(MQ, max(0, S + fdiv(n, TWO_M)))
def expHi(n):
    if not n < SM: raise ValueError("expHi out of range")
    return sqHi(MQ, cdiv(S * SM, SM - n))
def expI(X):
    if not X[1] < SM: return (0, 0, False)
    return (expLo(X[0]), expHi(X[1]), X[2])
def tanhI(X):
    if not 2 * X[1] < SM: return (0, 0, False)
    El = expLo(2 * X[0]); Eh = expHi(2 * X[1])
    return (S - cdiv(2 * S * S, El + S), S - fdiv(2 * S * S, Eh + S), X[2])
def sumI(L):
    lo = 0; hi = 0; ok = True
    for x in L: lo += x[0]; hi += x[1]; ok = ok and x[2]
    return (lo, hi, ok)
def dotWI(ws, X): return downBy(65536, sumI([mulZ(w, x) for w, x in zip(ws, X)]))
def z1I(c, b, T): return downBy(65536, add(mulZ(c, T), cst(b * S)))
def tI(p, q): return (p * P44, q * P44, True)
def layer1(P, T): return [tanhI(z1I(c, b, T)) for c, b in zip(P["W1"], P["b1"])]
def layer2(P, A1): return [add(dotWI(row, A1), cst(b * P48)) for row, b in zip(P["W2"], P["b2"])]
def sqI(X): return downBy(S, sqRaw(X))


def netAll(P, T, need2=True):
    A1 = layer1(P, T)
    S1 = [omsq(a) for a in A1]
    V = [downBy(65536, mulZ(c, s)) for c, s in zip(P["W1"], S1)]
    A2 = [tanhI(z) for z in layer2(P, A1)]
    S2 = [omsq(a) for a in A2]
    D = [dotWI(row, V) for row in P["W2"]]
    v = add(dotWI(P["W3"], A2), cst(P["b3"] * P48))
    d = dotWI(P["W3"], [mul(s, x) for s, x in zip(S2, D)])
    if not need2:
        return v, d, None
    Q = [downBy(65536, mulZ(c, downBy(65536, mulZ(c, x)))) for c, x in zip(P["W1"], [mul(a, s) for a, s in zip(A1, S1)])]
    D2 = [dotWI(row, Q) for row in P["W2"]]
    inner = [mul(s, add(d2, mul(a, sqI(x)))) for s, d2, a, x in zip(S2, D2, A2, D)]
    d2 = mulZ(-2, dotWI(P["W3"], inner))
    return v, d, d2


def emI(T): return expI(neg(T))
def rNI(P, T):
    v, d, _ = netAll(P, T, False); return add(add(d, v), neg(emI(T)))
def rdNI(P, T):
    v, d, d2 = netAll(P, T); return add(add(d2, d), emI(T))
def rHI(P, T):
    v, d, _ = netAll(P, T, False)
    return add(add(add(v, mul(T, d)), add(one, mul(T, v))), neg(emI(T)))
def rdHI(P, T):
    v, d, d2 = netAll(P, T)
    return add(add(add(mulZ(2, d), mul(T, d2)), add(v, mul(T, d))), emI(T))


def piece_bounds(R, Rd, P, a, b):
    """(lo, hi) with okR2 passing for [a, b] / 2^20, or None."""
    c = (a + b) // 2
    X = R(P, tI(c, c)); D = Rd(P, tI(a, b))
    if not (X[2] and D[2]): return None
    K = max(-D[0], D[1]); h = max(c - a, b - c)
    lo = (X[0] * 1048576 - K * h) // 1048576
    hi = -((-(X[1] * 1048576 + K * h)) // 1048576)
    return lo, hi


def okR(R, Rd, P, x):
    a, b, lo, hi = x
    c = (a + b) // 2
    X = R(P, tI(c, c)); D = Rd(P, tI(a, b))
    K = max(-D[0], D[1]); h = max(c - a, b - c)
    return (X[2] and D[2] and a <= c <= b and lo * 1048576 <= X[0] * 1048576 - K * h
            and X[1] * 1048576 + K * h <= hi * 1048576)


def chainOK(a, L):
    for x in L:
        if not (x[0] == a and x[0] < x[1] and x[2] <= x[3]): return False
        a = x[1]
    return a == 4194304


def okPt(num, G, H, E):
    return G[2] and H[2] and E[2] and 10000 * G[1] <= num * E[0] and -(num * E[0]) <= 10000 * H[0]


def seqOK(num, G, H, E, L, trace=None):
    for x in L:
        if not okPt(num, G, H, E): return False
        if trace is not None: trace.append((G, H, E))
        E2 = expI(tI(x[1], x[1])); dE = add(E2, neg(E))
        G = add(G, neg(mul(cst(x[2]), dE))); H = add(H, neg(mul(cst(x[3]), dE))); E = E2
    if trace is not None: trace.append((G, H, E))
    return okPt(num, G, H, E)


def load(path):
    n = json.load(open(path))
    assert n["denominator"] == 65536
    return {k: n[k] for k in ["W1", "b1", "W2", "b2", "W3", "b3"]}
