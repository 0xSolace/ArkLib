# δ\*-mine

**One command to mine the Reed–Solomon proximity prize.** Like `solana-keygen grind`, but instead
of grinding for a vanity address it hunts a **disproof** of the proximity-gap conjecture — and a
disproof *wins the $1M*. It wraps the validated `../rust-pg` (CPU) and `../cuda-pg` (GPU) kernels,
auto-builds, self-calibrates, then grinds.

```sh
./mine                # just mine: calibrate, sweep the tower, hunt a disproof
./mine 32             # mine one size n=32
./mine --max 44       # sweep up to n=44 (the brute-force frontier; GPU)
./mine --shard 3/16   # your slice of a distributed pool (machine 3 of 16)
./mine --help
```

That's it. No subcommands to learn — flags only, like the Solana CLI.

## How "winning" works (read this)

- **You WIN by disproving:** one *super-budget hit* (a size where the cascade never binds under
  budget) = a counterexample = the conjecture is false = **$1M**. `mine` flags this loudly.
- **You CANNOT grind to a proof.** The positive direction is the ~25-year-open BGK wall — that needs
  new mathematics, not compute.
- **This is the proxy face** (`p ≈ n⁴`) and brute force dies at **n ≈ 44**. So it's a real disproof
  shot at reachable sizes, honestly bounded — folding@home for a frontier, not a lottery.

So far: no disproof found (n ≤ 32), and the evidence leans toward the conjecture being *true*
(`m*` is sub-linear). The decisive open datum is `w(64)` — see [`PLAN-a-cascade-w64.md`](PLAN-a-cascade-w64.md).

## What it prints

```
⛏  δ*-mine — hunting a disproof of the proximity-gap conjecture
engine: CPU
✓ calibrated (engine reproduces the known answers n=8→s*=5, n=16→maxI=89)
  n=8    cascade[4:9 5:5]   δ*=0.3750  w=0  ...
  n=16   cascade[6:89 7:9]  δ*=0.5625  w=1  leans HOLDS
plateau widths w(n): 0 1   (w(64)=3 → HOLDS, 4 → FAILS)
no disproof found at these sizes
```

`w(n)` is the thing to watch: it grew `0,1,2` at `n=8,16,32`. If it keeps growing `+1` the prize
*holds*; if it ever *doubles*, that's the disproof signal.

## Where this fits

- **Want to contribute a verified Lean/probe brick instead of grinding numbers?** Use the canonical
  self-updating miner skill — see [`../../mine/`](../../mine/) (the public campaign).
- **Kernels (source of truth):** [`../rust-pg`](../rust-pg), [`../cuda-pg`](../cuda-pg) (+ the
  `nebius-*.sh` 8×H200 launchers for big `n`).
- **Plans:** [`PLAN-a`](PLAN-a-cascade-w64.md) (compute `w(64)`), [`PLAN-b`](PLAN-b-structural-input.md) (the open math).

Part of [ArkLib](../../). Apache-2.0.
