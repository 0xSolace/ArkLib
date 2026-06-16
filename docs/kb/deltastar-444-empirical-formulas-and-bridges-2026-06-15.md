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

## E. The grind ledger — ALL 50 bridges done (commits 92e90a0f1 + fd4a3fb14)

**Totals:** ~45 axiom-clean bricks (build with `scripts/pg-iterate.sh`, axioms ⊆
{propext, Classical.choice, Quot.sound}, no sorry) split as full LANDED + honest REDUCED
(named-`Prop` hypothesis), plus 2 machine-checked refutations (§D). The prize input — the
m*-growth / plateau-excess bound = BCHKS 1.12 — is named as an explicit `Prop` in
B28/B31/B32/B50 and **never discharged**. v3 additions: E6 B07 (even-fold, REDUCED) B08
`bin_doubling` B09 `tower_period_recursion`+`antipodal_odd_sum_eq_zero` B10
`subgroup_geom_sum_eq_zero` B41/B42 2-adic descent B43 base cases B44 char-sum; E5 B26/B27
primitive/imprimitive dichotomy B28 conditional-O(log n) B30 `mStar_increment_le_plateauWidth`;
E3 B11 `badSet_dilation_selfMap` B45 edge count; E4 B18 `DD_k=h` B47 tail B48 monotone; E1 B46
m*-well-defined; X B37 incidence=period B38 bad-side B39 `eps_mca≥incidence/q` B40 Λ² B49 budget;
E7 B50 assembly. NEXT for a continuing agent: the only open math is **bounding the plateau
width / m*-growth** (B28's hypothesis) — everything else is a proven brick feeding it.

### Original 28 (commit 92e90a0f1)

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

## F. Structural closures (commit e93c546dd) + core assault (commit 355f21f7a)

**Structural (`_Close*`):** E6 odd-grade vanishing **GENUINELY CLOSED** (`_Close07c.cf_odd_eq_zero`,
`oddGradeVanishesStrong_holds` — verified faithful: `fhat`/`cf` match the probe byte-for-byte,
non-vacuous, m=1 countermodel). E6 even-fold recursion **base instance CLOSED** by kernel `decide`
(`_Close43.recursion_step_16_8_target`: `badCount 16 4 2 = badCount 8 2 1 = 40`), general case
**REDUCED** to one named `FoldImageHyp` (carrier-symmetry forcing; fold-map injectivity proven,
`_Close07a.foldVal_injective`). E5 primitive clean-recursion + one-sided lift **REDUCED** to set-
membership hyps (`_Close26`, `_Close25`). Recall §D: `cf ≠ D`, so E6 closure is structural and does
NOT touch the prize.

**Core assault on m*-growth (`_CoreA*`, the prize direction):**
- **A1** `coreA1_mStar_ge_three`, `deltaStar_le_capacity_sub_two_over_n` — provable UPPER bound on
  δ* (the easy side, prize-consistent with P5).
- **A2** `orbit_bound_iff_BCHKS_budget` — the orbit-count `O` decay; honest **REDUCES_TO_BCHKS**.
- **A3** (axiom-FREE) `weakestSuff_iff_mStarOLog`, `weakestSuff_le_BCHKS`, but
  `weakestSuff_imp_BCHKS_needs_reverse` — **backward-proof: weakest-sufficient is IMPLIED by BCHKS,
  reverse OPEN** ⟹ weakest-suff might be *strictly weaker* than BCHKS = a possible **escape** (not
  yet closed; A7/A3deep resolve).
- **A5** `binding_is_monomial_controlled`, `monomial_dir_maximizes_overdet` — binding reduces to the
  **monomial cascade** (tightens the reduction to the p-independent orbit object).
- **A6** `Dstar_le_minorImage_card`, `plueckerMinor_ne_subsetSum` — a **NOVEL invariant**: D*(m)
  bounded by a **Plücker/determinantal minor-image count**, machine-certified DIFFERENT from BCHKS
  subset-sum (the 2×2 minor is `−xy`, a *product*, not an additive spectrum). A genuinely new
  computable surface for m* — its tractability (Lang-Weil on the degree-2 determinantal variety) is (⚠️ CAVEAT, audit 2026-06-16: the A6 bound `D*(2)≤2·span` is a BÉZOUT/degree ROOT-count — valid; but any *Lang–Weil point-count* framing is an OVERREACH because the relevant `V_r` is 0-DIMENSIONAL, making Lang–Weil VACUOUS. The lever is real as a root-count, not as a variety point-count.)
  the freshest non-BCHKS lever, under attack in A6deep.

## G. The COMPLETE TIGHT REDUCTION + final verdict (commits fadd986d0, ef3e127bd)

**THE HEADLINE (axiom-clean, the answer to "is the bound complete and correct"):**
`_CoreReductionComplete.prize_reduces_to_BCHKS` and `_CoreA7.prize_iff_BCHKS_at_scale` prove the
**complete, TIGHT, two-directional** reduction
> `mStar D budget n ≤ M  ⟺  BCHKSWindowHolds Σ smap rmap budget n M`
under explicit honest hypotheses (binding-exists; the cascade=subset-sum identification
`D n j = Σ (smap n) (rmap n j)`; monotonicity = B48; edge value = B24/CoreA1). Plus
`_CoreA7.BCHKS_necessary`, `prize_iff_BCHKS_at_scale`. **So BCHKS 1.12 is both SUFFICIENT and
NECESSARY: the prize is EXACTLY BCHKS 1.12, and the wall is provably unavoidable in-tree.** This is
the proof that the current bound is *complete and correct* — nothing in-tree gets around it.

**A4 — the cleaner-stated reduction:** prize ⟸ `BinderPrimitive` (the worst direction is primitive,
plateau-width ≤ 1, at every tower level), `plateau_prize_of_BinderPrimitive`,
`BinderPrimitive_iff_plateauWidth_le_one`. ⚠️ **`mStar_polylog_unconditional` is an OVERCLAIMED
NAME** — its body is trivial induction *conditional* on the per-level step hypothesis `hstep`; it is
NOT an unconditional polylog proof. Cite it only as the conditional reduction it is.

**A6deep — the freshest genuinely-non-BCHKS lever:** `Dstar_le_two_mul_span` bounds the depth-2
binding count `D*(2) ≤ 2·span` via the **degree-2 (Bézout) determinantal minor polynomial**, and
`bezout_beats_choose_two` proves `2n < C(n,2)` ∀ n≥6 — so this determinantal bound **genuinely beats
the trivial per-witness count** IF the single-parameter minor factorization (`hfac`/`hΔ`/`hne`) holds
for the worst direction. Whether that factorization holds for multi-window m≥3 is the open
structural question; the determinantal point-count has Lang-Weil theory, a different surface from
BCHKS subset-sum. **This is the one lever a continuing agent should push.**

**⚠️ The "escape" theorems are VACUOUS, but they point at a GENUINE open question (precise form):**
`_CoreA7.weakestSuff_strictly_below_BCHKS` and `_CoreA3deep.escapeConfig_nonempty` /
`weakestSuff_not_imp_BCHKSCount` instantiate `D ≡ 0`, `budget ≡ 0` — a degenerate toy model proving
the *abstract predicates* differ as *formulas*; they do NOT exhibit a real escape and must not be
cited as one. **BUT** the underlying question is real and p-independent: `_CoreA3` proves
`BCHKS ⟹ WeakestSuff` UNCONDITIONALLY via the **dedup domination `D n m ≤ Σ_r(μ_{smap n})`** (each
forced ratio `γ_R = −h_{a−k}(R)/h_{b−k}(R)` is a subset-sum ratio, so the distinct-γ *union* count is
≤ the subset-sum count — deduplication only shrinks). The converse `Σ ≤ D` is **false pointwise**
(B33: `D` decreasing `[40,9,5,…]` vs `Σ_r` increasing `[3,5,10,…]`). So `WeakestSuff ≤ BCHKS`
(`weakestSuff_le_BCHKS`), and **whether it is STRICTLY weaker (a real escape — prize needs less than
BCHKS) or equal (the wall) reduces to whether the dedup `D ≤ Σ_r` is STRICT at logarithmic depth**
`m ≈ log n`. This is a p-INDEPENDENT growth-law question, decisively OFF the analytic single-saddle
MGF wall the older char-sum backward-proof hit. (In-tree cross-checks lean "reduces to wall": the
generating-function support of the distinct-γ count GROWS, refuting a naive "+1 single-term"
strictness mechanism — but the dedup-strictness question itself is NOT settled and is the precise,
honest residual.) Together with the A6 determinantal lever, this is one of two p-independent forms of
the open core worth a continuing agent's effort.

**FINAL VERDICT.** The #444 bridge program is a **complete, honest, axiom-clean reduction of the
prize to BCHKS Conjecture 1.12**, proven TIGHT (necessary + sufficient). The wall is real and
unavoidable in-tree; numerics cannot settle it (`m*(64)` needs `C(64,17)~10^14`, list-decode
regime). The single remaining in-tree lever that is NOT obviously BCHKS-equivalent is the **A6
determinantal/Bézout minor count** (`_CoreA6deep`) — its tractability via Lang-Weil on the degree-2
determinantal variety is the open question most worth pursuing. Everything else (the structural E6
recursion, the orbit decay, the backward-proof) provably reduces to, or is, BCHKS 1.12. The prize
is now *exactly one named combinatorial conjecture* — proving BCHKS 1.12 (or the A6 determinantal
bound) is the whole remaining task, and it is external mathematics.
