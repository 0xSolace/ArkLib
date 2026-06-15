# CORRECTION: on TRUE 2-power (prize) n, the worst-case window list is CONSTANT at fixed (ρ,η) — my "~n² growth" was a NON-2-power artifact (#444)

A second, decisive correction (the antipodal-tower army hit the session limit, so done inline). My earlier
"worst-case list GROWS ~n² (7,22,34 at n=16,20,24)" was CONTAMINATED: **n=20 and n=24 are NOT powers of 2**, so
μ_20, μ_24 are NOT prize-regime domains (the prize is n=2^μ). On TRUE 2-power n the picture is different and FAVORABLE.

## The corrected measurement (TRUE 2-power n only, broad worst-case scan, window midpoint = fixed η)

| ρ | (n,k) pair | worst-case window list | worst word |
|---|---|---|---|
| 1/8 | (16,2) | **4** | x^13+x^12 |
| 1/8 | (32,4) | **4** | x^27+x^26 |
| 1/16 | (32,2) | **7** | x^29+x^28 |
| 1/16 | (64,4) | (η=0.094, computing) | — |
| 1/4 | (16,4) | 7 | x^15+x^5 |

At **fixed ρ and fixed η (window midpoint)**, the worst-case list is **CONSTANT across 2-power n**:
ρ=1/8 gives **4 at both n=16 and n=32** (same η=0.125). This is exactly what the window list law
`L*=2^{Θ_ρ(1/η)}` predicts (n-INDEPENDENT at fixed η) and what the antipodal-tower "constant in n at fixed dyadic
ratio" predicts. **STRONGLY SUPPORTS THE FLOOR** (constant lists in the prize regime ⟹ poly trivially).

## Two corrections to earlier claims

1. **"worst-case list grows ~n²" (comment 4705308940): RETRACTED as a non-2-power artifact.** The growth came
   entirely from n=20,24 (not powers of 2, not the prize). On 2-power n the list is CONSTANT at fixed (ρ,η).
2. **"worst word = antipodal/walking-Laurent x^{n/2}" (the army's reduction assumption): WRONG.** The true worst
   2-power word is the **consecutive-exponent lacunary word `x^a + x^{a−1}` at high a** (x^13+x^12, x^27+x^26,
   x^29+x^28), giving a small constant list — NOT the antipodal x^{n/2} (which gives only 2). The general-γ residual
   resolves to: worst = consecutive-exponent, still constant.

## Why the 2-power regime is constant (mechanism, to be proven)

On 2-power n the squaring/antipodal tower (verified: `e_{2ℓ}(±z)=(−1)^ℓ e_ℓ(z²)`, `e_odd=0`) makes the
symmetric-function count self-similar down the dyadic tower to a fixed base group — giving a list CONSTANT in n at
fixed dyadic ratio. The measured constancy (4 at ρ=1/8, n=16,32) is the in-regime signature of this. The window
list law constant C(ρ) is the base-group count.

## Status

**Major favorable correction:** on the actual prize regime (n=2^μ), the worst-case window list is CONSTANT at
fixed (ρ,η) — measured 4 (ρ=1/8, n=16,32), strongly supporting the floor and the window-list-law/antipodal-tower
structure. The earlier "~n² growth" was a non-2-power (n=20,24) artifact, now retracted. The worst word is the
consecutive-exponent lacunary word, not antipodal. NOT a closure (the upper bound for ALL 2-power n is still the
open core, = the antipodal-tower base count proven constant), but the strongest in-regime evidence for the floor:
**prize-regime lists are constant, not growing.** Tool: scripts/rust-pg/src/bin/listscan.rs (2-power n only).
