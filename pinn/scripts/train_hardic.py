"""Train u(t) = 1 + t*N(t) (N: 1->32->32->1 tanh) for u' = -u + exp(-t) on [0, 4]; the initial condition holds exactly.
Same recipe as the first network (float64, Adam then L-BFGS, input scaling folded into layer 1, weights rounded to k/2^16)."""
import json, time
import numpy as np, torch

torch.set_default_dtype(torch.float64)
torch.manual_seed(0)
net = torch.nn.Sequential(torch.nn.Linear(1, 32), torch.nn.Tanh(), torch.nn.Linear(32, 32), torch.nn.Tanh(), torch.nn.Linear(32, 1))


def uhat(t):
    return 1 + t * net(t / 2 - 1)


def residual(t):
    t = t.clone().requires_grad_(True)
    u = uhat(t)
    du = torch.autograd.grad(u.sum(), t, create_graph=True)[0]
    return du + u - torch.exp(-t)


grid = torch.linspace(0, 4, 2001)[:, None]
opt = torch.optim.Adam(net.parameters(), lr=3e-3)
sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, 6000)
t0 = time.time()
for step in range(6000):
    t = torch.cat([grid, 4 * torch.rand(1000, 1)])
    opt.zero_grad(); L = (residual(t) ** 2).mean(); L.backward(); opt.step(); sched.step()
dense = torch.linspace(0, 4, 8001)[:, None]
lb = torch.optim.LBFGS(net.parameters(), lr=1, max_iter=20000, history_size=100, tolerance_grad=1e-14,
                       tolerance_change=1e-16, line_search_fn="strong_wolfe")
def closure():
    lb.zero_grad(); L = (residual(dense) ** 2).mean(); L.backward(); return L
for _ in range(3):
    lb.step(closure)
print(f"trained in {time.time() - t0:.0f} s, loss {(residual(dense) ** 2).mean().item():.3e}", flush=True)
W1 = net[0].weight.detach().numpy()[:, 0] / 2
b1 = net[0].bias.detach().numpy() - net[0].weight.detach().numpy()[:, 0]
ws = [W1, b1, net[2].weight.detach().numpy(), net[2].bias.detach().numpy(), net[4].weight.detach().numpy()[0],
      float(net[4].bias.detach().numpy()[0])]
D = 2 ** 16
ints = [np.round(np.asarray(x) * D).astype(np.int64) for x in ws]
json.dump({"definition": "u(t) = 1 + t * N(t), N(t) = sum_j W3[j] * tanh( sum_i W2[j][i] * tanh(W1[i] * t + b1[i]) + b2[j] ) + b3; "
                         "every weight is the integer given here divided by `denominator`",
           "denominator": D, "denominator_log2": 16, "W1": ints[0].tolist(), "b1": ints[1].tolist(), "W2": ints[2].tolist(),
           "b2": ints[3].tolist(), "W3": ints[4].tolist(), "b3": int(ints[5])}, open("data/net_hardic.json", "w"), indent=0)
print("saved data/net_hardic.json", flush=True)
