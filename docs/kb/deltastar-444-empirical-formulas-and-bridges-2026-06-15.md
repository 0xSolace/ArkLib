# δ* — the empirical formulas that pin it, and the bridge program (#444)

**Date:** 2026-06-15. **Purpose:** State the empirical (numerically-pinned, true-but-unproven
or only-partly-proven) formulas that determine `δ*`, then drive a grind of *bridge attempts* —
proofs that build from the proven substrate **up to** these formulas. Each bridge attempt yields
either an axiom-clean Lean brick or an honest reduction naming the exact remaining gap.

`δ*` = the mutual-correlated-agreement / list-decoding threshold of explicit dyadic Reed–Solomon
`RS[μ_n, k]`, `k = ρn`, prize regime `n = 2^μ ~ 2^30`, `q = n^β` (β≈4–5), budget `q·ε* ≈ n`,
`ε* = 2^-128`. Window interior target: `1−√ρ` (Johnson) `< δ* <` `1−ρ` (capacity).

---

## A. The proven anchors (foundation bricks — already axiom-clean in-tree)

- **P1 — Binding ⟺ incidence budget (the converse pin).** `OpenCoreConverse.lean`:
  `deltaStar_iff_incidence_budget` — `δ < mcaDeltaStar C (E/|F|) ↔ WorstCaseIncidenceBounded C δ E`
  (both directions). So `δ*` is *exactly* the budget-crossing of the worst far-line incidence.
- **P2 — Far-line incidence = period sum.** `IncidencePeriodBridge.lean`:
  `lineIncidence = Σ_{b : b·s₁ = 0} conj(η_b)·ψ(b·s₀)`, and `incidence_l2_eq_period_l2`.
- **P3 — Orbit closed form (off-binding).** `OrbitCountCrossingLaw.lean`: `crossing_law` —
  `D = N·S`, `S·d = n ⊢ D ≤ n ↔ N ≤ d`. The monomial bad-γ set is a union of
  `γ ↦ γ·h^{b−a}` orbits (orbit size `S = n/gcd(b−a,n)`).
- **P4 — Period parallelogram / dyadic Gauss recursion.** `DyadicTowerRecursion.lean`:
  `η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}` and the second-moment parallelogram law.
- **P5 — Upper bracket (constant gap below capacity).** `DeltaStarConstantGapBelowCapacity.lean`,
  `MCADeltaStarCapacity.lean`: `δ* ≤ 1 − ρ − c_ρ`, `c_ρ ≈ ρ/127`, via the averaging list lower
  bound `maxList(1−(k+t)/n) ≥ C(n,k+t)/q^t`. Plus UDR lower `δ* ≳ (1−ρ)/3`.
- **P6 — Height-gate vacuity at prize scale.** `HeightGateBindingDepthVacuity.lean`: the natural
  root-sum-norm route is *proven vacuous* at `n = 2^30` binding depth (LEVER H dead at prize).

---

## B. The empirical formulas that pin δ* (bridge TARGETS)

Notation: `m = s − k` = over-determination depth; `m*` = binding depth (first `m` whose worst
far-line incidence drops `≤ budget`). `D*(m)` = worst-direction over-det far-line incidence at
depth `m`. All cascade data is `ρ = 1/4`, exact char-0 (prime `p ≡ 1 mod n`, `p ≫ n^4`),
reproduced this session by `scripts/rust-pg` (`orbcount`, `dirworst`).

- **E1 — Master gap identity.** `capacity − δ* = (m*−1)/n`, i.e. `δ* = 1 − ρ − (m*−1)/n`.
  *Status:* elementary unwinding of P1 + the definition of `m*`. **Should be a clean brick.**

- **E2 — The binding cascade (reproduced).**
  - `n=8,  k=2`: `D*(m) = [40, 9, 5, 1, 1]` (m=1..5), binding `m*=3`, `δ*=0.500` (= Johnson).
  - `n=16, k=4`: `D*(m) = [3936, 89, 9, 9, 9, 8, 1, 1, 1]`, binding `m*=3`, `δ*=0.625` (> Johnson).
  - `n=32, k=8`: `D*(m) = [—, 4096, 89, 89, 9, …]` (prior GPU), binding `m*=5`, `δ*≈0.625`.
  - So `m* = 3, 3, 5`; `δ*` already **past Johnson** for `n≥16`.

- **E3 — Orbit closed form + partial-orbit binding.** For monomial dir `(x^a,x^b)`:
  `D = z + S·O`, `z∈{0,1}`, `S = n/gcd(b−a,n)`, crossing `D ≤ n ⟺ O ≤ gcd(b−a,n)`.
  **Empirical refinement (this session):** at the *binding* `s*` the worst direction is
  **primitive** (`d=1`, `S=n`) and `D` is **not** a multiple of `S` — the bad set is a *partial*
  orbit (n=8: binder (5,4), D=5≠8·O; n=16: binder (11,10), D=9≠16·O). The clean crossing law
  governs the *plateau*, a partial-orbit count governs the *crossing*.

- **E4 — Leading value + geometric decay.** `D*(1) ≈ n³` (n=16: 3936 ≈ 16³=4096). The cascade
  decays by a factor `≈ n/2…n/4` per depth step (16: 3936→89→9 ≈ ×44, ×10). So from `~n³` to
  budget `n` is `≈ 2` decay steps **plus the plateau width** ⇒ `m* ≈ 2 + (plateau width)`.

- **E5 — Dyadic cascade recursion (PARTIAL).** `D*_{2n}(m) = D*_n(m−1)` holds at shallow depth
  but **breaks at the binding** via *plateau-doubling*: `n=32`'s worst-dir cascade has a doubled
  `89`-rung (m=3 AND m=4), the extra rung pushing `m*` from 3 to 5. If clean it gives
  `m*(2n) ≤ m*(n)+1 ⇒ m* = O(log n)`; the open quantity is the **plateau excess per tower level**.

- **E6 — EXACT FFT-graded recursion.** With `#bad_n(k,m)` = number of distinct nonzero
  `n/2`-binned graded frequency vectors over `(k+m)`-subsets `A ⊆ ℤ/n` with all lower graded
  pieces zero:
  `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`  and  `#bad_{2n}(k, odd) = 0`.
  *Status:* verified **exactly, all cases** at 16↔8 (`probe_2adic_tower_recursion.py`, "ALL HOLD").
  This is a clean 2-adic self-similarity of the graded obstruction (the antipodal `−1∈μ_{2n}`
  kills odd graded pieces; the doubling map folds subsets). **Looks fully provable** — a bijection
  + an antipodal-involution vanishing. **Highest-value clean target.**

- **E7 — m* growth (THE PRIZE).** `m* = 3,3,5` ⟹ conjecturally `m* = O(log n)`, equivalently
  `δ* → 1−ρ − c_ρ`. ⟺ **BCHKS Conjecture 1.12** (distinct r-fold subset-sum count
  `|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m`). p-INDEPENDENT combinatorial object (off the *analytic* BGK
  char-sum wall) but OPEN. The whole bridge program chips at this through E3–E6.

---

## C. Bridge architecture

Build from {Gauss sums, divided differences `DD_k(x^a) = h_{a−k}` (complete homogeneous symmetric
in the nodes), Schur `s_λ` at roots of unity, cyclotomic norms, P1–P6} **up to** E1–E6, and
through them squeeze E7. Each bridge attempt returns an honest verdict:
`LANDED (axiom-clean Lean)` | `REDUCED to ⟨named statement⟩` | `FAILED because ⟨obstruction⟩`.

The grind log lives in this directory; landed bricks are recorded in
`deltastar-444-LANDED-bricks-API-2026-06-15.md`.

## D. Corrections from the grind (machine-checked refutations — do NOT re-assume)

- **E4's `D*(1) ~ (n/2−1)²` is FALSE.** `_BridgeB24.dedge_ne_quadratic_claim` proves
  `(2m−1)² < Dedge m` for `m ≥ 3` (decide-checked instances 9,37,97,201,361,589). The `(n/2−1)²`
  value is the *deeper* over-det (`s−k ≥ 2`) p-independent count, NOT the edge `D*(1)`, which is
  `~ n³` (n=16: 3936 ≈ 16³). The two were conflated; keep only `D*(1) ~ n³` (E4 leading).
- **The naive object identity `D*(m) = |Σ_r(μ_s)|` (r-fold subset-sum count) is FALSE.**
  `_BridgeB33.objectIdentity_false`: `D*(1)=40` (n=8,k=2) but `|Σ_1|=3` at `s=3`, forcing `40=3`.
  D* (distinct *forced-γ* count) is NOT the subset-sum count directly; the correct relation is the
  weaker threshold reduction `_BridgeB33.bridge_threshold_of_BCHKS` (BCHKS budget ⟹ incidence
  budget), which is the honest E7 link. So E7's "⟺ BCHKS 1.12" is a *sufficient-direction*
  reduction (`mStar_le_iff_BCHKS` packages the equivalence at the budget level), not a raw
  object equality.

## E. The grind ledger (28 axiom-clean bricks landed, commit 92e90a0f1)

E1: B01 `deltaStar_master_gap_identity`/`capacity_gap_eq`, B02 `deltaStar_gt_johnson_iff_mstar_lt`,
B03 `one_le_bindingDepth`, B04 `capacity_sub_deltaStar*`. E3: B12 fixed-point ≤1, B13
`orbitSize_eq` (=n/gcd), B14 `crossing_law_budget_n`, B15 `partial_orbit_not_multiple`, B16
`primitive_binder_orbit_le_one`, B17 `orbit_dvd_incidence_sub_fixed`. E4: B19 `Dstar1_eq_of_bridge`
(forced-γ count), B20 `Dstar1_le_choose`, B21 `overdet_agreement_affine_iff`, B22
`multiWindow_*`, B23 `cascade_geometric_decay`/`cascade_binds_by_depth`, B24 `dedge_*`. E5: B25
`lift_crossing`, B29 `mStar_tower_shift`/`mStar_tower_shift_prize` (the m*(2n)≤m*(n)+1 lever). E6:
B05/B06 antipodal odd-vanishing core, _Bridge05. E7: B31 `mStarOLog_iff_BCHKS1_12`, B32
`tendsto_deltaStar_capacity_of_mStar_little_o`, B33 `bridge_threshold_of_BCHKS`. X: B34
`monomial_dir_maximizes`, B35 `odd_graded_moment_eq_zero`, B36 `dividedDifference_eq_zero_iff_rs_member`.
The single remaining OPEN input across all of E5/E7 is the **plateau-excess / m*-growth bound**
(= BCHKS 1.12), named as an explicit `Prop` hypothesis in B28/B31/B32/B50, never discharged.
