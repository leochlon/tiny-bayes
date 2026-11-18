"""Train a 1->32->32->1 tanh PINN for u' = -u + exp(-t), u(0) = 1 on [0, 4]; round its weights to exact dyadic fractions.

Training uses the scaled input s = t/2 - 1 in [-1, 1]; the scaling is folded into the first layer afterwards, so the
saved network is exactly N(t) = W3 . tanh(W2 tanh(W1 t + b1) + b2) + b3 with t itself as input.
"""
import json, math, sys, time
import numpy as np, torch

torch.set_default_dtype(torch.float64)
torch.manual_seed(0)
T0, T1 = 0.0, 4.0
net = torch.nn.Sequential(torch.nn.Linear(1, 32), torch.nn.Tanh(), torch.nn.Linear(32, 32), torch.nn.Tanh(), torch.nn.Linear(32, 1))


def scaled(t):
    return net(t / 2 - 1)


def residual(t):
    t = t.clone().requires_grad_(True)
    u = scaled(t)
    du = torch.autograd.grad(u.sum(), t, create_graph=True)[0]
    return du + u - torch.exp(-t)


def loss_fn(t):
    r = residual(t)
    ic = scaled(torch.zeros(1, 1)) - 1
    return (r ** 2).mean() + 10 * (ic ** 2).sum()


grid = torch.linspace(T0, T1, 2001)[:, None]
opt = torch.optim.Adam(net.parameters(), lr=3e-3)
sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, 6000)
t0 = time.time()
for step in range(6000):
    t = torch.cat([grid, T0 + (T1 - T0) * torch.rand(1000, 1)])
    opt.zero_grad(); L = loss_fn(t); L.backward(); opt.step(); sched.step()
    if step % 2000 == 0:
        print(f"adam {step} loss {L.item():.3e}", flush=True)
dense = torch.linspace(T0, T1, 8001)[:, None]
lb = torch.optim.LBFGS(net.parameters(), lr=1, max_iter=20000, history_size=100, tolerance_grad=1e-14,
                       tolerance_change=1e-16, line_search_fn="strong_wolfe")


def closure():
    lb.zero_grad(); L = loss_fn(dense); L.backward(); return L


for rnd in range(3):
    L = lb.step(closure)
    print(f"lbfgs round {rnd} loss {loss_fn(dense).item():.3e}", flush=True)
print(f"trained in {time.time() - t0:.0f} s", flush=True)

# fold s = t/2 - 1 into layer 1: W1 s + b1 = (W1/2) t + (b1 - W1)
W1 = net[0].weight.detach().numpy()[:, 0] / 2
b1 = net[0].bias.detach().numpy() - net[0].weight.detach().numpy()[:, 0]
W2 = net[2].weight.detach().numpy(); b2 = net[2].bias.detach().numpy()
W3 = net[4].weight.detach().numpy()[0]; b3 = float(net[4].bias.detach().numpy()[0])


def evaluate(p, t):
    """N, N' and the residual at the points t (float64, exact formulas)."""
    W1, b1, W2, b2, W3, b3 = p
    z1 = np.outer(t, W1) + b1; a1 = np.tanh(z1)
    z2 = a1 @ W2.T + b2; a2 = np.tanh(z2)
    N = a2 @ W3 + b3
    da1 = (1 - a1 ** 2) * W1                      # d a1 / dt
    dz2 = da1 @ W2.T
    dN = ((1 - a2 ** 2) * dz2) @ W3
    return N, dN, dN + N - np.exp(-t)


def stats(p):
    t = np.linspace(T0, T1, 400001)
    N, dN, r = evaluate(p, t)
    err = (1 + t) * np.exp(-t) - N
    i, j = np.argmax(np.abs(r)), np.argmax(np.abs(err))
    N0 = evaluate(p, np.array([0.0]))[0][0]
    return dict(delta=abs(N0 - 1), rho=float(abs(r[i])), rho_at=float(t[i]), E=float(abs(err[j])), E_at=float(t[j]))


exact = (W1, b1, W2, b2, W3, b3)
print("float64 network:", stats(exact), flush=True)
best = None
for k in (12, 14, 16, 18, 20, 24):
    D = 2 ** k
    q = [np.round(np.asarray(x) * D) / D for x in exact]
    s = stats(q)
    maxnum = max(int(np.max(np.abs(np.round(np.asarray(x) * D)))) for x in exact)
    print(f"rounded to 1/2^{k}: {s}  largest numerator {maxnum}", flush=True)
    if best is None and s["rho"] <= 1.01 * stats(exact)["rho"] and s["E"] <= 1.01 * stats(exact)["E"]:
        best = k
k = best or 24
D = 2 ** k
ints = [np.round(np.asarray(x) * D).astype(np.int64) for x in exact]
out = {"definition": "N(t) = sum_j W3[j] * tanh( sum_i W2[j][i] * tanh(W1[i] * t + b1[i]) + b2[j] ) + b3; "
                     "every weight is the integer given here divided by `denominator`",
       "denominator": D, "denominator_log2": k,
       "W1": ints[0].tolist(), "b1": ints[1].tolist(), "W2": ints[2].tolist(), "b2": ints[3].tolist(),
       "W3": ints[4].tolist(), "b3": int(ints[5])}
json.dump(out, open("data/net.json", "w"), indent=0)
q = [np.asarray(x, dtype=np.float64) / D for x in ints]
print("saved data/net.json with denominator 2^%d; float64 stats of the saved network:" % k, stats(q), flush=True)
