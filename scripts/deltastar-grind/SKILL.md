---
name: proximity-grind
description: Grind the RS proximity-gap far-line incidence cascade D*_n(m) on CPU/GPU to extend the 2-power tower data and hunt for a disproof — with a mandatory calibration gate and honest reporting. Use when asked to "grind", extend the cascade/tower, compute w(n)/m*, or hunt a counterexample for the δ* / proximity prize.
---

# proximity-grind

Reusable workflow for grinding the proximity-gap frontier with `scripts/deltastar-grind/grind`.

## When to use

- "grind the tower / extend the cascade / compute `w(n)` or `m*`"
- "hunt for a disproof / counterexample of the floor"
- any δ* far-line incidence computation on the **proxy face** (`p ≈ n⁴`)

Do **not** use this to "prove the prize" — see Honesty below. This grinds evidence, not proofs.

## Steps

1. **Doctor + build.** `scripts/deltastar-grind/grind doctor` — confirms `cargo` (CPU) and/or
   `nvcc` (GPU) and builds the kernels (`rust-pg`, `cuda-pg`).
2. **CALIBRATION GATE (never skip).** `grind validate` must pass before any output is trusted:
   `n=8 → s*=5, δ*=0.3750` and `n=16 → s=6 maxI=89, s*=7, δ*=0.5625`. If it fails, the kernel is
   buggy — stop, do not report numbers.
3. **Pick the right `n`.** CPU ≤ 24 (laptop), GPU for 28–44, nothing past 44 (brute wall). Check
   the feasibility note `grind` prints; if `n > 44`, say so and stop — that regime needs the closed
   form, not this tool.
4. **Grind.** `grind tower [MAXN]` for the growth law; `grind run N [K]` for one cascade;
   `grind hunt N` for disproof mode (flags super-budget / `×2` anomalies).
5. **Distribute if large.** `grind shard N K A0 A1` emits `SHARD n k a b s maxI` work units; a
   coordinator takes the max over direction-shards. Every node re-runs `validate`.
6. **Report honestly.** Use the template below. Always state which face (proxy) and the brute wall.

## Honesty (hard rules — this is the point of the tool)

- It grinds the **proxy face** (`p ≈ n⁴`), **not** the real cryptographic-`p` BGK wall.
- Brute force **dies at `n ≈ 44`** — it can add data points, never *settle* additive-vs-multiplicative.
- It can **DISPROVE** (one super-budget / `×2`-doubling counterexample = decisive) but can **never
  PROVE** the conjecture. Never claim otherwise. If a run "looks like it solves it," it doesn't.
- A `×2` doubling (`w(2n)=2w(n)`) or a non-binding cascade is a real disproof signal — flag loudly,
  cross-check at a second prime, then report to issue #444.

## Report template

```
proximity-grind — n=<N> k=<K> (ρ=1/4, proxy p≈n⁴) on <CPU|GPU>
  calibration: PASS (n=8 s*=5; n=16 maxI=89 s*=7)
  cascade D*_<N>(m): <s:maxI …>   s*=<>, δ*=<>, w(<N>)=<>
  tower so far: w = <…>  → leaning <additive/holds | multiplicative/fails | unsettled>
  CAVEAT: proxy face only; brute wall at n≈44; evidence not proof.
```

## Maintenance

If you hit a new kernel quirk, a faster shard strategy, or a clearer feasibility boundary, update
this file and `README.md`. Keep the calibration values in sync with `rust-pg`/`cuda-pg` ground truth.
