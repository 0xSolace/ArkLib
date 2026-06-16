# δ\*-grind

A distributed grinder for the **Reed–Solomon proximity-gap frontier** — the open core of the
$1M Ethereum proximity-gap prize. Think `solana-keygen grind`, but instead of hunting a vanity
key prefix it grinds the **over-determined far-line incidence cascade** `D*_n(m)`, maximizing
over directions at each agreement depth, on a laptop or a GPU server.

It wraps two **already-validated** kernels (no reinvented math):

| path | kernel | when |
|------|--------|------|
| CPU | [`scripts/rust-pg`](../rust-pg) (Rust + rayon) | always (auto-built with `cargo`) |
| GPU | [`scripts/cuda-pg`](../cuda-pg) (`pg.cu`) | when `nvcc` is present (≈400–2000× faster) |

---

## ⚠ Honest scope — read this, it is the whole point

This tool **grinds evidence and hunts a disproof.** It does **not**, and **cannot**, prove the prize.

1. **Brute force dies at `n ≈ 44`.** The `C(n, s)` term explodes; no GPU farm reaches asymptotic
   `n`. So this tool can never *settle* the additive-vs-multiplicative question — only add data points.
2. **It computes the PROXY face** (prime `p ≈ n⁴`), not the real cryptographic-`p` BGK wall
   `M(μ_n) ≤ C·√(n·log(p/n))`. Even infinite compute decides the proxy, not the $1M.
3. **A grinder can DISPROVE but never PROVE.** One super-budget / `×2`-doubling counterexample at
   accessible `n` would be decisive. The positive conjecture is a ~25-year-open analytic
   number-theory problem; grinding accumulates evidence, it does not close it.

This is **folding@home for a math frontier**, not a lottery ticket. If anyone tells you "run this
and win $1M," they are wrong.

---

## What it grinds (the science)

For the smooth-domain RS code on the 2-power subgroup `μ_n ⊂ F_p*`, the exact threshold reduces to
the growth of the worst-direction incidence cascade `D*_n(m)` down the **2-power tower**:

- `incidence(a,b;s)` = # distinct `γ ∈ F_p` such that `x^a + γ·x^b` agrees with a degree-`<k`
  polynomial on `≥ s` points of `μ_n` (via the over-determined divided-difference witness).
- `D*_n(m)` = max over far directions `(a,b)` at agreement `s = k+m`.
- `w(n)` = run-length of the constant pre-binding value `89 = 1 + 11·8` in the cascade.

The whole prize reduces to **one dichotomy** ([issue #444](https://github.com/lalalune/ArkLib/issues/444)):

> Does `w(n)` grow **additively** (`w(2n)=w(n)+c` ⟹ `m*=O(log n)` ⟹ prize HOLDS direction)
> or **multiplicatively** (`w(2n)=2w(n)` ⟹ `m*` linear ⟹ prize FAILS)?

Recorded: `w = 0, 1, 2` at `n = 8, 16, 32`. The decisive datum is **`w(64) ∈ {3 additive, 4 mult}`**.
The current lean is *favorable* — `m*(32)=5` is sub-linear (`≠ 7`) — but it's unsettled, and it's
the proxy face.

---

## Quick start

```sh
./grind doctor          # detect toolchain, build CPU (and GPU if nvcc) kernels
./grind validate        # CALIBRATION GATE — must pass before trusting any output
./grind tower           # grind the 2-power tower, print the w(n) growth law
./grind run 24          # grind one cascade (n=24, k=6, ρ=1/4)
./grind hunt 32         # disproof mode — flag super-budget / ×2 anomalies
```

`validate` is the heart of the trust model: it refuses to call a kernel trustworthy until it
reproduces the ground-truth oracle (`n=8 → s*=5, δ*=0.3750`; `n=16 → s=6 maxI=89, s*=7,
δ*=0.5625`). A kernel that misses these is buggy and its big-`n` output is meaningless.

### Feasibility by `n`

| `n`      | where | time |
|----------|-------|------|
| ≤ 24     | laptop CPU | seconds–minutes |
| 28–32    | CPU slow / GPU | minutes–hours / seconds |
| 36–44    | **GPU only** | the brute-force frontier |
| > 44     | nobody | `C(n,s)` explodes — needs the closed form, not this tool |

---

## Distributed grinding

`incidence` is embarrassingly parallel over `(direction × subset)`. To split one big `n` across
many machines, shard by direction:

```sh
# machine i of M grinds directions a ∈ [i·n/M, (i+1)·n/M):
./grind shard 40 10 0 10     # emits:  SHARD n k a b s maxI
./grind shard 40 10 10 20
# … a coordinator takes the max over shards per (s) to assemble D*_40(m).
```

Laptops take small `n`; GPU servers take `n ≥ 36`. The `validate` gate runs on every node, so a
buggy contributor can't poison the aggregate. (A reference coordinator is left as a thin script /
future work — the work-unit format `SHARD n k a b s maxI` is the contract.)

---

## Plans

- [`PLAN-a-cascade-w64.md`](PLAN-a-cascade-w64.md) — compute `w(64)`, the proxy-face tie-breaker.
- [`PLAN-b-structural-input.md`](PLAN-b-structural-input.md) — the real (open) structural input.

## Skill

[`SKILL.md`](SKILL.md) packages the grind + calibration gate + honest-report template as a
reusable agent workflow.

---

Part of [ArkLib](../../). Apache-2.0. The kernels (`rust-pg`, `cuda-pg`) are the source of truth;
this is the friendly distributable wrapper around them.
