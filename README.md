# tiny-bayes

Pythia-14M in Lean 4, by Hassana Labs. EleutherAI/pythia-14m (revision `cf967c0a9a04383db6f7b1108d86b2962634b4ac`) defined exactly over ℝ in Lean 4 and Mathlib: all 14,067,712 parameters as float16 bit patterns, decoded exactly, and the GPT-NeoX forward pass with exact GELU. Every theorem in each folder's `Main.lean`, and every final theorem of `point/` and `poisson/`, depends only on `propext`, `Classical.choice` and `Quot.sound`.

| Folder | Namespace | Contents | Modules | Theorems | Build |
|---|---|---|---|---|---|
| `exact/` | `CON` | exact model, kernel-certified outputs, Bayesian-in-expectation results | 158 | 35 | 13 min |
| `interval/` | `PRO` | proved-sound interval evaluator, red/blue encoding | 51 | 14 | 9 min |
| `induction/upper_bound/` | `CON` | `TripleCert → ¬Claim`; bound of 941 tokens | 164 | 29 | 4 min |
| `induction/lower_bound/` | `PRO` | normal form; `CleanCert → ClaimAt 9` | 117 | 29 | 40 s |
| `collapse/` | `CE` | repetition theorems for every set of weights | 4 | 3 | 35 s |
| `pinn/` | `PINN` | physics-informed networks certified through their residuals | 207 | 18 | 3 min |
| `point/` | `PythiaCert` | a full-vocabulary decision and an adversarial example on a 32-token prompt | 1,567 | 5 | 19.5 CPU h |
| `poisson/` | `PoissonR3` | error bound for a trained PINN on the whole unit square | 2,463 | 6 | 42.7 CPU h |

Build times are from scratch with 24 to 40 parallel Lean processes; for `point/` and `poisson/`, total CPU time.

## Model (`exact/CON`)
- `W/`: one `Nat` per row of float16 bits; `F16.lean` decodes them; `Pythia.lean` assembles `pythia14m`.
- `Model.lean`: LayerNorm (ε = 1e-5), rotary embeddings on 8 of 32 dimensions per head, causal softmax attention, parallel attention and MLP, GELU x·Φ(x) with Φ an integral.
- `Cert.lean`, `Gauss.lean`, `Cert2.lean`, `K/`: interval arithmetic proved sound over ℝ, a proved enclosure of the Gaussian integral, and per-layer kernel checks for one-token prompts.

## Bayesian in expectation
Does the tiny-transformer result (a separate Lean development, `TinyBayes`: order averages within 0.0034 of Laplace's rule on every bag with n ≤ 8, with order gaps) hold for Pythia-14M?

`exact/`:
- `length_blind`: for any weights, on a prompt repeating one token, the last hidden state does not depend on the length.
- `main`, `main_all_params`: on the native prompt (no BOS), for every token pair, readout and set of weights, the order averages are not within any ε < 7/60 of Laplace's rule on the bags with 1 ≤ n ≤ 8.
- Kernel-certified after `<|endoftext|>`: P("1")/(P("0")+P("1")) ∈ [0.980688, 0.980689] (`bos_empty_17_18`); " 1" against " 0": [0.912424, 0.912426] (`bos_empty_470_337`). `main_bos`: with BOS, both encodings fail the tiny statement.
- On the red/blue encoding of `interval/` (an earlier version, in `CON/PRO/`): the empty bag is 0.40769 (`pro_empty_bag`), and the native probabilities of ` red` and ` blue` sum to less than 3·10⁻⁷ (`pro_candidates_native_mass`). Under `Cert8`, the order averages are not within 0.1426 of Laplace's rule (`pro_hypothesis_refutes_laplace`) or within 0.044 of the posterior predictive of any prior on [0, 1] (`pro_hypothesis_refutes_every_prior`). The tolerances of `TinyTheorem` admit a predictor that is not monotone in the evidence (`pro_criterion_admits_antimonotone`).

`interval/`: prompt `<|endoftext|>`, then ` red,` for 1 and ` blue,` for 0; `p x` = P(red)/(P(red)+P(blue)).
- `enclosure`: for every binary sequence x, p x ∈ pI x, using proved enclosures of exp, √, π, cos/sin and GELU.
- `main`: 0.4076930531 ≤ p [] ≤ 0.4076930534, from 25 kernel checks composed by `layer_ok`.
- `main8 : Cert8 → TinyTheorem p 8 0.143 0.073 0.52`: on all 45 bags with n ≤ 8, the order averages are within 0.143 of Laplace's rule and 0.073 of Beta(2, 9/4), with an order gap of 0.52.
- `con_criterion_rejects_exact_bayes`: the 0.0034 Laplace criterion of `exact/` rejects the Jeffreys posterior predictive for every ε < 1/12.
- `scripts/red_blue_table.py`: float64 evaluation of the Hugging Face model on the 511 prompts with n ≤ 8; prints the 45 order averages in the layout of `tbl` and checks them against it, their deviations from Laplace's rule (the orange points of Figure 2) and the order gap of `Numerics8`.

At the tiny model's tolerance of 0.0034 the result does not extend to Pythia-14M.

## Induction (`induction/`)
Claim: there are V′ ⊆ V with |V′| ≥ 1,000 and δ > 0 such that, for every sequence [BOS, r₁, …, rₘ, r₁, …, rₘ] of distinct rᵢ ∈ V′ with 3 ≤ m ≤ 8, at each position of the second copy holding r_k with 2 ≤ k ≤ m − 1, the logit of r_{k+1} exceeds every other logit of the 50,304-token vocabulary by at least δ. V is the first 5,000 token ids from 500 upward that decode to a space followed by at least two letters.
- `upper_bound/`: `main : TripleCert → ¬Claim`. `TripleCert` lists 638,716 statements "pythia-14m fails on some order of these three tokens" over 167 token groups; the combinatorics are kernel-checked (`search_ok`, `search_sound`, `cover_ok`, `caps3_total`, `capacities_exclude`). `main_bound3`: under `TripleCert`, induction fails on every subset of V with more than 941 tokens; `main_bound`: 831 under `GroupCert` (sequences of up to five tokens).
- `lower_bound/`: `claim_iff_normalForm` (the margin plays no role; each case is one next-token comparison on a prompt of 6 to 16 tokens), `cleanCert_claimAt : CleanCert → ClaimAt 9` (nine named tokens), `bracket`.
- The two formalisations are proved equivalent (`PRO.claim_iff_opp`, `CON.pro_claim_iff`).
- `scripts/triple_search.py`: the float32 search that produces `freeMasks` from the groups of `Data.lean`, and a float64 recheck of the failing order and competitor it finds for each `TripleCert` statement.
- `scripts/triple_cert.py`: float64 check of every `TripleCert` statement, all six orders against all 50,304 logits (`--sample N` for a random subset).
- `scripts/clean_cert.py`: float64 check of the 623,448 sequences of `CleanCert` against all 50,304 logits.

## Collapse (`collapse/`)
For every set of weights (`= t` elaborates to `= some t`):

```lean
theorem collapse (θ : Params) (t : Token) (n : ℕ) (hn : 0 < n) :
    nextLogits θ (List.replicate n t) = nextLogits θ [t]

theorem eternal (θ : Params) (t : Token) (ht : strictArgmax (nextLogits θ [t]) = t) (k : ℕ) :
    greedy θ [t] k = List.replicate (k + 1) t
```

`CE/Model.lean` is `exact/CON/Model.lean` in the namespace `CE`; `CE/Spec.lean` defines `nextLogits`, `strictArgmax`, `argmax` and greedy decoding. `collapse` is the logit form of `length_blind`; `eternal` follows by induction on k.

## PINN (`pinn/`)
Two 1→32→32→1 tanh networks trained for u′ = −u + e⁻ᵗ, u(0) = 1 on [0, 4], with weights rounded to k/2¹⁶: N (`data/net.json`), and Ñ (`data/net_hardic.json`) with the initial condition built in, û(t) = 1 + t·Ñ(t). Both are certified through their own residuals, without using the exact solution.
- `part1`: for every M continuously differentiable on [0, 4], every partition 0 = a₀ < … < a_K = 4 and every lo_k ≤ M′(s) + M(s) − e⁻ˢ ≤ hi_k on [a_k, a_{k+1}], every solution u satisfies e⁻ᵗ(1 − M(0)) − Σₖ hi_k w_k(t) ≤ u(t) − M(t) ≤ e⁻ᵗ(1 − M(0)) − Σₖ lo_k w_k(t), where w_k(t) = ∫ e^{−(t−s)} ds over [a_k, a_{k+1}] ∩ [0, t].
- `part2_named`, `part2`: the 508-piece certificate `certN` bounds N's residual and keeps both sides within 2·10⁻⁴, so every solution is within 2·10⁻⁴ of N on [0, 4].
- `part3_named`, `part3`: the 652-piece certificate `certH` does the same for û, within 3·10⁻⁴.
- `transfer_N`, `transfer_H`: every C¹ model with the same initial value whose residual lies within a certificate's bounds satisfies the same error bound.

The residual bound on each piece is a kernel-checked mean-value enclosure: the residual at the midpoint, widened by a bound on its derivative (the networks' second derivative is proved), in outward-rounded integer interval arithmetic at scale 2⁶⁴ with exp and tanh proved sound over ℝ. On each piece the two sides of `part1` are affine in e⁻ᵗ, so checking them at the partition points covers all of [0, 4]. Evaluated exactly at the partition points, the two sides stay within 1.43·10⁻⁴ for N and 2.20·10⁻⁴ for û; the largest errors against the exact solution are 1.01·10⁻⁴ and 1.68·10⁻⁴.

`scripts/` has the training scripts, a 50-digit reference evaluation of both models and their residuals (`reference.py`), an exact Python copy of the interval arithmetic (`mirror.py`), and the scripts that regenerate the certificate modules (run from `pinn/`: `python3 scripts/partition.py 9e-5 1.1e-4 cert.json && python3 scripts/emit.py cert.json`).

## Decision and adversarial example (`point/`)
`tokens` (`Input.lean`) is a 32-token prompt, BOS first. `perturbInput δ` adds δ : Fin 128 → ℝ to the input embedding at position 31, before the first layer; `witnessVector` (`WitnessNorm.lean`) is a fixed dyadic vector, and its norm is the sup norm.

```lean
theorem actual_frozen_point_pair :
    (∀ j : Fin 50304, j.val ≠ 10166 →
      (2 : ℝ) ≤ CON.logit CON.pythia14m tokens 10166 -
        CON.logit CON.pythia14m tokens j.val) ∧
    ‖witnessVector‖ = (37/16384 : ℝ) ∧
    (1/20 : ℝ) ≤
      CON.logitFrom CON.pythia14m (perturbInput witnessVector) 10895 -
        CON.logitFrom CON.pythia14m (perturbInput witnessVector) 10166
```

- `actual_center_margin` (`PointCertificate.lean`): token 10166 beats each of the other 50,303 logits by at least 2.
- `actual_center_hidden_enclosed`, `actual_witness_hidden_enclosed`: the final hidden states at the prompt and at the perturbed input lie in the stored boxes `Output.center` and `Output.witness`.
- `CON/` holds the model, the float16 decoder (`F16.lean`) and the 403 parameter modules (`CON/W/`). `PointChecks/` (694 modules) checks the forward pass layer by layer, `OutputChecks/` (197) the unembedding over the vocabulary, and `PointData/` (198) holds the boxes they check.
- `POINT_THEOREM_TYPES.txt`: each final theorem's statement and axioms, as printed by the build.
- `checkpoint_binding.json`: the SHA-256 of `model.safetensors` and the shape, byte offsets and SHA-256 of each of its 76 tensors. `INDEPENDENT_CHECKPOINT_PROVENANCE.json` rebuilds every tensor's bytes from the literals in `CON/W/` (401 files, each with its SHA-256) and matches all 76 hashes.

## Poisson PINN (`poisson/`)
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

## Build
Lean v4.27.0-rc1 and Mathlib `fdddb3ea` (`lean-toolchain`, `lake-manifest.json`; `lake exe cache get` fetches a prebuilt Mathlib). Set `LEAN_BIN` to the `lean` binary and `LEAN_BASE_PATH` to the output of `lake env printenv LEAN_PATH`, then:

```sh
sh induction/restore_weights.sh        # copies exact/CON/W into both induction folders
shasum -a 256 -c SHA256SUMS
python3 tools/project.py build exact CON --jobs 40
python3 tools/project.py build interval PRO --jobs 24
python3 tools/project.py build induction/upper_bound CON --jobs 24
python3 tools/project.py build induction/lower_bound PRO --jobs 24
python3 tools/project.py build collapse CE --jobs 8
python3 tools/project.py build pinn PINN --jobs 40
python3 tools/project.py build point . --jobs 40
python3 tools/project.py build poisson . --jobs 40
```

`python3 tools/project.py check <NS> <dir> <tag>` rebuilds a folder from scratch in a fresh workspace, rejects `sorry`, `axiom`, `native_decide` and similar escapes, and prints each theorem of `Main.lean` with the axioms it depends on. `tools/gen_weights.py` and `tools/gen_bits.py` regenerate `W/` and `Bits/` from `model.safetensors`.

## Citation
If you use or cite this work, please credit Hassana Labs:

```bibtex
@misc{hassanalabs2026tinybayes,
  title  = {tiny-bayes: Pythia-14M and physics-informed networks in Lean 4},
  author = {{Hassana Labs}},
  year   = {2026},
  url    = {https://github.com/leochlon/tiny-bayes}
}
```

## License
CC BY-NC 4.0 (`LICENSE`): free to use and adapt for non-commercial purposes, with attribution to Hassana Labs. Commercial use is not permitted. The pythia-14m parameters in `exact/CON/W` and `*/Bits` are EleutherAI's, under Apache 2.0.
