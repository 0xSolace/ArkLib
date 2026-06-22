<!-- #444 / Paley-BGK. The house/conjugate reframe + the 104-angle MAX-vs-AVERAGE meta-theorem
(2026-06-22). M = house(eta_1) = max Galois conjugate of one Gaussian period; 104 angles across ~70
fields, 0 bound the max; the precise structural no-go (symmetric=geomean, resonance=lower-bound, only
3 max-native genera all consuming the prize as input) + the single missing ingredient + the live
frontier (effective per-coset Deligne-Katz discrepancy). NOT closure; the sharpest map to date. -->

# The House/Conjugate Reframe and the 104-Angle MAX-vs-AVERAGE Meta-Theorem

## 0. The reframe

`M = max_{b!=0}|eta_b|` equals the **house** (largest absolute Galois conjugate) of a single Gaussian
period `eta_1 = sum_{x in mu_n} zeta_p^x`, an algebraic integer of degree `f=(p-1)/n` in the
degree-`f` subfield of `Q(zeta_p)`. The whole spectral family `{eta_b}_{b!=0}` is one Galois orbit
(`f` conjugates, `eta_b` constant on cosets `b*mu_n`). So the prize `M <= C sqrt(n log(p/n))` is a
**bounded-house / Lehmer-flavoured statement for the specific Gaussian-period family**.

## 1. Three exact facts that pin the target (axiom-clean / exact)

- **(F1) Real-rooted.** `-1 in mu_n` (dyadic `n`) makes every `eta_c` real (`x<->-x` pairing,
  `max|Im eta_c| < 6e-15`). `{eta_c}` is `f` real numbers; `trace = sum_c eta_c = -1`;
  `sum_c eta_c^2 = p - n` exactly.
- **(F2) The max is a strictly isolated peak.** `#{c : |eta_c| > 0.9*house} = 1` uniformly
  (`n=16,32,64`). The house is a single dominant conjugate, not one of a cluster.
- **(F3) Sub-iid Gaussian extreme, from below.** `house ~ RMS * sqrt(2 ln f) = sqrt(2 n ln(p/n))`,
  with `C_iid = house/sqrt(2n ln f) = 0.848, 0.891, 0.964 -> 1` from below (`RMS|eta| = sqrt n`
  exact). The conjugates obey the **iid-Gaussian extreme law**, approached from below — **iid-like,
  NOT log-correlated** (no `-3/2 loglog` correction). The prize `<=>` the `f` real conjugates have a
  **sub-iid-Gaussian right tail to the `f`-extreme**.

## 2. The 104-angle MAX-vs-AVERAGE meta-theorem

104 angles were invented across ~70 fields (analytic NT, potential theory/heights, probability/EVT,
homogeneous & arithmetic dynamics, additive combinatorics, arithmetic geometry, spectral/RMT,
harmonic analysis, math-physics/Coulomb-gas/KPZ/spin-glass, and exotic: condensed math, o-minimality,
resurgence, motivic-Galois, tropical/Berkovich). Every angle that produced an unconditional upper
bound gave only a **floor** (`M <= sqrt(p-n) = Theta(sqrt(nm))`, the 2nd-moment/Weil wall). The
structural reason, now a sharp **no-go with an exception clause**:

1. **Symmetric / permutation-invariant** functionals of the conjugate multiset — Mahler measure,
   Norm, discriminant, capacity / transfinite diameter, every `2r`-moment / energy, restriction
   `L^p`, EKR signed sums, Petsche discrepancy, Schur-Siegel-Smyth / Schur LP — read the **geomean /
   energy average**, which the house exceeds by the *growing* EVT factor `sqrt(2 log f)` (measured
   `house/geomean = 4.1, 5.4` at `n=16,32`, `~ sqrt(log f)`). They **cannot** see the max by
   construction.
2. **Variational / resonance** functionals — Bondarenko-Seip resonator, Soundararajan resonance,
   GCD-sums, Lovasz theta — are one-sided **lower-bound** devices (`sup_{R>=0} Rayleigh = house`
   exactly): wrong inequality direction. They restate `M`, never cap it. (And `hat-eta(j) = sqrt p`
   flat for all `j != 0`, so the GCD-sum arithmetic saving is vacuous — back to the `sqrt p` floor.)
3. **The only escape classes are three max-native genera**, and all three consume the *same* input:
   - **(a) generic chaining / Dudley** on the conjugate field — needs uniform per-conjugate
     sub-Gaussian `psi_2` tail;
   - **(b) Stein-Chen Poisson** for the high-conjugate count `N_t = #{c: eta_c > t sqrt n}` — needs a
     uniform Berry-Esseen marginal tail (F2 is positive evidence the `Poisson(lambda->0)` edge regime
     holds);
   - **(c) per-coset effective equidistribution** (Deligne-Katz / Chebotarev with power-saving) —
     needs an *effective* per-`b` discrepancy at the `f`-extreme.

   Each is **logically equivalent to the prize**, not a route around it:
   `MAX bound  <==  per-conjugate sub-Gaussian tail  <==>  sum_c eta_c^{2r} <= Wick at r* ~ (1/2) log f  <==>  PRIZE`.

## 3. The single missing ingredient (sharpest form)

> A right-tail bound on **one** conjugate's distribution that uses the **sign cancellation among the
> `f` real periods** — the mechanism that pushes the house *below* the `sqrt(p-n)` 2nd-moment/Weil
> floor. Equivalently: the `f` real conjugates are sub-iid-Gaussian to the `f`-extreme (F3,
> `C_iid -> 1`). Equivalently: `E_r <= (2r-1)!! n^r` (char-0 Wick, no wraparound surplus) to depth
> `r* ~ (1/2) log f ~ log p`. Equivalently: the wraparound surplus `W_r = E_r - Wick` (positive from
> onset `r_0 = 5`, concentrated at `r ~ log p`) stays slack-bounded at log depth.

This is invisible to every magnitude/symmetric functional precisely because **sign cancellation among
real periods is not a function of the value-multiset** — it lives in the arithmetic of *which*
conjugate carries *which* sign (the per-`b` data that affine-blind — additive invariants constant on
`b*mu_n` — and phase-blind — `sum_b` polynomials are real counts — functionals annihilate).

## 4. The live frontier

The honest place to push: **#3, effective Deligne-Katz / Chebotarev per-coset equidistribution** — the
*only* angle whose error term is intrinsically per-conjugate (`b`-tracking, non-affine-blind) rather
than an integrated/averaged one — feeding the chaining (#a) or right-edge large-deviation (#4) bound.
The unsolved analytic-NT core is an *effective* (not merely qualitative Sato-Tate) per-coset
discrepancy at the `f`-extreme; the naive Weil bound returns `sqrt p` (the floor). The ordered Frobenius
orbit (`c -> c+1`) is the one genuinely non-symmetric handle (van der Corput / Wiener-Wintner on the
ordered orbit) and is almost entirely unexploited — high-risk, high-reward.

## 5. Verdict

**Not solved.** Zero of the 104 angles bound `M <= C sqrt(n log p)`; the only unconditional upper
bounds are the `sqrt(p-n)` floor and the moment-optimized `sqrt2 * prize` *conditional* on the open
Wick bound, which fails at the depth it is needed (`E_9/Wick = 1.27 > 1` at `n=32`). The durable
deliverable is the **taxonomy**: every symmetric invariant reads the geomean, every resonance is a
lower bound, and the three max-native genera consume the prize as input — the `~68th` independent
confirmation of one wall, now localized to the per-coset sign-cancellation right-tail at `beta=4`.
No QED is claimed.
