# Physics-informed networks

Trained physics-informed networks with error bounds proved against the solutions of their equations.

| Folder | Namespace | Contents | Modules | Theorems | Build |
|---|---|---|---|---|---|
| `poisson/` | `PoissonR3` | error bound for a trained PINN on the whole unit square | 2,463 | 6 | 42.7 CPU h |
| `ode/` | `PINN` | physics-informed networks certified through their residuals | 207 | 18 | 3 min |

Build times are from scratch with 24 to 40 parallel Lean processes; for `poisson/`, total CPU time.

## Poisson (`poisson/`)
N(x, y) = p(x)p(y)(b₀ + Σₕ aₕ tanh(wₕ₁x + wₕ₂y + bₕ)), with p(t) = t(1 − t), 16 tanh units and 65 weights over 2²⁴ (`Frozen.lean`), solves −Δu = f on (0, 1)² with u = 0 on the boundary. U(x, y) = p(x)p(y)e^{xy}, f = −ΔU (`manufactured_pde`), Q = [0, 1]² and `witness` = (100/256, 97/256).

```lean
theorem frozen_bracket
    (u : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q) (hdu : CoordTwoOn u)
    (hbu : ∀ z ∈ Q, Edge z → u z.1 z.2=0)
    (hpu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=forcing x y) :
    (∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ certU) ∧
      certL ≤ |N witness.1 witness.2-u witness.1 witness.2|

theorem frozen_reference_accuracy :
    (∀ z ∈ Q, |N z.1 z.2-U z.1 z.2| < (1:ℝ)/30000) ∧
      (1:ℝ)/80000 ≤ |N witness.1 witness.2-U witness.1 witness.2|
```

- `PinnCertFarm.hres`: |−Δ(N − C) − f| ≤ certR on (0, 1)², for the polynomial correction C (`Correction.lean`). The square is covered by 9,163 closed cells (`exact_cover_leaf_count`), checked in 2,291 shards (`RawShard*.lean`) and assembled by `allValid` and `hres_closed`.
- `hC`: |C| ≤ certA on Q. A maximum-principle bound with barrier constant 3/40 (`Maximum.lean`) turns certR into the error bound certU = certA + 3·certR/40; `hpoint` gives the lower bound at `witness`. The constants are integers over 2⁶⁴ (`Candidate.lean`), and certU/certL < 2.52.
- `frozen_reference_bracket`: `frozen_bracket` for U, which `reference_is_solution` proves is a solution.
- `FINAL_THEOREM_TYPES.txt`: each final theorem's statement and axioms, as printed by the build.

## ODE (`ode/`)
Two 1→32→32→1 tanh networks trained for u′ = −u + e⁻ᵗ, u(0) = 1 on [0, 4], with weights rounded to k/2¹⁶: N (`data/net.json`), and Ñ (`data/net_hardic.json`) with the initial condition built in, û(t) = 1 + t·Ñ(t). Both are certified through their own residuals, without using the exact solution.
- `part1`: for every M continuously differentiable on [0, 4], every partition 0 = a₀ < … < a_K = 4 and every lo_k ≤ M′(s) + M(s) − e⁻ˢ ≤ hi_k on [a_k, a_{k+1}], every solution u satisfies e⁻ᵗ(1 − M(0)) − Σₖ hi_k w_k(t) ≤ u(t) − M(t) ≤ e⁻ᵗ(1 − M(0)) − Σₖ lo_k w_k(t), where w_k(t) = ∫ e^{−(t−s)} ds over [a_k, a_{k+1}] ∩ [0, t].
- `part2_named`, `part2`: the 508-piece certificate `certN` bounds N's residual and keeps both sides within 2·10⁻⁴, so every solution is within 2·10⁻⁴ of N on [0, 4].
- `part3_named`, `part3`: the 652-piece certificate `certH` does the same for û, within 3·10⁻⁴.
- `transfer_N`, `transfer_H`: every C¹ model with the same initial value whose residual lies within a certificate's bounds satisfies the same error bound.

The residual bound on each piece is a kernel-checked mean-value enclosure: the residual at the midpoint, widened by a bound on its derivative (the networks' second derivative is proved), in outward-rounded integer interval arithmetic at scale 2⁶⁴ with exp and tanh proved sound over ℝ. On each piece the two sides of `part1` are affine in e⁻ᵗ, so checking them at the partition points covers all of [0, 4]. Evaluated exactly at the partition points, the two sides stay within 1.43·10⁻⁴ for N and 2.20·10⁻⁴ for û; the largest errors against the exact solution are 1.01·10⁻⁴ and 1.68·10⁻⁴.

`scripts/` has the training scripts, a 50-digit reference evaluation of both models and their residuals (`reference.py`), an exact Python copy of the interval arithmetic (`mirror.py`), and the scripts that regenerate the certificate modules (run from `pinn/ode/`: `python3 scripts/partition.py 9e-5 1.1e-4 cert.json && python3 scripts/emit.py cert.json`).

## Build
From the repository root, with `LEAN_BIN` and `LEAN_BASE_PATH` set as in the [top-level README](../README.md#build):

```sh
python3 tools/project.py build pinn/ode PINN --jobs 40
python3 tools/project.py build pinn/poisson . --jobs 40
```
