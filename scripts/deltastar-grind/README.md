# δ\*-grind — local CPU/GPU front-door for the cascade compute

A small, calibration-gated CLI for running the over-determined far-line incidence cascade
`D*_n(m)` on **your own laptop or GPU box**. It is a thin, honest wrapper around the existing
validated kernels — it does **not** replace anything; it just makes the *numerical* path easy to
run locally with a trust gate baked in.

## This is part of a bigger campaign — start there

- **Want to contribute a verified brick (proof or refutation)?** Use the canonical, self-updating
  miner skill — not this. See [`../../mine/`](../../mine/): `mine the proximity prize: read
  https://deltastar-paper.pages.dev/mission.md and follow it`. That is the crowd-mining front door.
- **The kernels** (source of truth): [`../rust-pg`](../rust-pg) (CPU), [`../cuda-pg`](../cuda-pg)
  (GPU + `validate.sh` + the `nebius-*.sh` 8×H200 launchers). This CLI builds and drives those.
- **The proof-brick grinders:** [`../wf/bridge-grind*.mjs`](../wf).

## What this adds (and only this)

A unified `doctor / validate / run / tower / hunt / shard` front-door over `rust-pg`+`cuda-pg`:
auto-selects GPU if `nvcc` is present else CPU, **refuses to report until the calibration oracle
passes**, and adds laptop-friendly `tower` (the `w(n)` growth law), `hunt` (disproof framing), and
`shard` (direction work-units for splitting one big `n` across machines).

```sh
./grind doctor      # build CPU (and GPU if nvcc) kernels
./grind validate    # calibration gate: n=8→s*=5, n=16→s=6 maxI=89 s*=7  (must pass)
./grind tower       # the 2-power tower → w(n) additive-vs-multiplicative read
./grind run 24      # one cascade; ./grind hunt 32 ; ./grind shard 40 10 0 10
```

## ⚠ Honest scope (same as the campaign — restated so it's on the box)

Grinds **evidence** and hunts a **disproof** on the **proxy face** (`p≈n⁴`). Brute force dies at
`n≈44`. It can **disprove** (one super-budget / `×2`-doubling counterexample = decisive) but can
**never prove** the conjecture — that's the open ~25-year BGK wall, not a compute target. Not a
lottery. See [`MISSION.md`](../../mine/MISSION.md) for the authoritative rules.

## Plans

- [`PLAN-a-cascade-w64.md`](PLAN-a-cascade-w64.md) — compute `w(64)`, the proxy-face tie-breaker.
- [`PLAN-b-structural-input.md`](PLAN-b-structural-input.md) — the real (open) structural input.

Part of [ArkLib](../../). Apache-2.0.
