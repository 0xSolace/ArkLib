/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipCensusSharpened
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
-- §2.3 live reduction dossier (#371 closed, #389 open):
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarPinAllWitness
import ArkLib.Data.CodingTheory.ProximityGap.PinBeyondJohnson
import ArkLib.Data.CodingTheory.ProximityGap.PackingDeepBandMiss
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBelowUDR
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiberCodewordList
import ArkLib.Data.CodingTheory.ProximityGap.MonomialSupplyChoose
-- §2.5 live routes (LD⇒MCA frontier):
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import ArkLib.Data.CodingTheory.ProximityGap.CurveCloseSetTargetBound
import ArkLib.Data.CodingTheory.ProximityGap.FoldedCurveCloseSetBound
import ArkLib.Data.CodingTheory.ProximityGap.SeparationSurvivalCount
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignLineDecodable
-- §2.6 GM-MDS route:
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma22
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep
import ArkLib.Data.CodingTheory.GMMDS.LovettDivisibility
-- §3 THE SHAW OPERATOR — the unified unknown + the closed prize conjecture:
import ArkLib.Data.CodingTheory.ProximityGap.ShawOperator

/-!
# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║   THE PROXIMITY PRIZE WORKBENCH  ·  one file, everything you need, write here  ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

**Mission (proximityprize.org / ABF26 = Arnon–Boneh–Fenzi 2026, ePrint 2026/680).**
Produce a *novel, complete, closed* conjecture (no further open math, no incomputable lemma)
that **simultaneously resolves both grand challenges** for *explicit, constant-rate, smooth*
Reed–Solomon codes in the **prize regime** — and prove it. The two challenges are the same
δ* up to the LD⇒MCA bridge; the genuine open core is ONE object (§3).

────────────────────────────────────────────────────────────────────────────────
## §0.  THE PRIZE REGIME — pin this or you are wasting time
────────────────────────────────────────────────────────────────────────────────
* Code: `C = RS[F, L, k]`, `L` a **smooth** (FFT/NTT, multiplicative-subgroup `μ_n`)
  evaluation domain, `n = |L| = Fintype.card ι`.
* Rate: `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}` — **constant rate**, so `k = Θ(n)` (`prizeRates`).
* Threshold: `ε* = 2^(-128)` (`epsStar`); operationally `q·ε* ≈ n` for `q ≈ n·2^128`.
* Field: `q = |F|` large, `q ≈ n·2^128` (so `q·ε* ≈ n`); positive rate `0 < k`.
* Target window: pin `δ*` in the **window interior** `(1−√ρ, 1−ρ−Θ(1/log n))` — the
  beyond-Johnson, below-capacity band. Johnson `1−√ρ` is already done; capacity `1−ρ` is
  the wall. **Anything that reduces to Johnson, to capacity-for-constant-DIM, or to an
  incomputable lemma is OUT.**

⚠️ **DEGENERACY TRAP (do not target these).** The *real-valued* `grandMCAChallenge` /
`grandListDecodingChallenge` collapse: `grandMCAChallenge_iff_epsMCA_one` (radius-one only),
and `not_grandListDecodingChallengeRS_of_pos` (the LD one is *false* for `0<k`, `ε*<1`).
**The faithful targets are `mcaConjecture` (§1) and the operational `mcaDeltaStar` (§2).**

────────────────────────────────────────────────────────────────────────────────
## §1.  THE EXACT TARGET  (prove ONE of these — they are the prize)
────────────────────────────────────────────────────────────────────────────────
**(T1) The uniform MCA conjecture** `ProximityGap.mcaConjecture` (ABF26 §4.5):
  `∃ c₁ c₂ c₃, ∀ RS[F,L,k], ∀ δ < 1−ρ,  ε_mca(RS,δ) ≤ (1/q)·n^{c₁}/(ρ^{c₂}·η^{c₃})`,
  `η = 1−ρ−δ`. Constants quantified BEFORE the ∀-over-codes. Proving this resolves the
  MCA prize at every rate (`nonempty_mcaLowerWitness_of_mcaConjecture` → `mcaPrize`).
**(T2) A `GrandMCAResolution`** for each prize rate: a maximal `δ*` with `ε_mca(C,δ*)≤ε*`
  and strict failure above. Equivalent to pinning the operational `mcaDeltaStar` (§2).
**(T3) Either ⟹ the LD prize** via the LD⇒MCA bridge (`GG25MCAFromCurveDecodability`,
  the §3.x curve-decodability route) — the two challenges share `δ*`.

The `YOUR CONJECTURE HERE` slot at the bottom is where the closed-form `δ*(ρ,ε*,n)` and its
proof go. It must be **complete**: a single computable `δ*`-expression, proven, no residual.

────────────────────────────────────────────────────────────────────────────────
## §2.  THE SUBSTRATE  (PROVEN, axiom-clean, ready to apply — build on these)
────────────────────────────────────────────────────────────────────────────────
**The governing law** (`MCAThresholdLedger`):
  `mcaDeltaStar C ε* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}`.
  · `le_mcaDeltaStar_of_good`  — lower bound on δ* from a good radius (incidence ≤ q·ε*).
  · `mcaDeltaStar_le_of_bad`   — upper bound on δ* from a bad witness.
  · `FarCosetExplosion.epsMCA_ge_far_incidence` — `ε_mca ≥ incidence/q` (the law's engine).

**Capacity side — SOLVED for constant DIMENSION `k=O(1)`** (NOT the prize, but the template):
  · `KKH26CeilingMarch.interiorCeiling_march` — worst-case `incidence(1−r/2^μ) ≤ C(n,r)/r`
    (iSup over ALL stacks), ⟹ FFT-domain RS reaches `δ*=(1−ρ)−1/n` for `k=O(1)`.
  · `KKH26CeilingMarch.march_badScalars_card_mul_le` — `#bad·(d+2) ≤ C(n,d+2)` (the count).

**Granularity ladder** (`GranularityLadderRS.mcaDeltaStar_rs_eq_granularity`):
  `δ* = j/n` on bands `3(j−1)+k ≤ n`, `j+1+k ≤ n`, `j+1 ≤ q`, `ε*∈[j/q,(j+1)/q)`. EXACT.

**Boundary law** (`BoundarySupExactness.rs_boundary_epsMCA_eq`):
  `ε_mca(RS, δ) = n/q` for `3∣n`, `6<n`, `k=n−4`, `2 ≤ δ·n < 3`.

**Ownership count — PROVEN TIGHTLY BRACKETED** (`OwnershipCensusSharpened`):
  · `sharpened_badScalars_card_mul_choose_le` — `#bad·C(w₀+1,d+1) ≤ C(n,d+1)·(n−d−1)` (LOWER).
  · `deviation_ownership_card` — the CEILING: deviation stacks realize EXACTLY `C(w−1,d+1)`,
    so NO per-witness-subset bound can do better. **This surface is PROVEN EXHAUSTED (§3).**
  · `sharpened_epsMCA_le` — wires the sharpened count to `epsMCA`.

**Energy / sub-Johnson list chain** (`GVHBKEnergyReduction`, `AdditiveEnergyRepBound`):
  `GVRepBound G M` (`r(c)≤4|G|^{2/3}`) ⟹ `E(G)³ ≤ 260|G|⁸` ⟹ list `T ≲ n^{11/6} ≪ n²`.
  **√-loss is FATAL** (`T² ≤ |G|·E`; even `E=|G|²` → list `n^{3/2}`, sub-Johnson not capacity).

**Paper-bound bridges** (`GrandChallenges`, all wired to witnesses):
  GKL24 `MCALowerWitness.ofLinearOnePointFiveJohnsonGKL24`, BCHKS25 `…ofJohnsonBCHKS25` /
  `…ofJohnsonJumpBCHKS25AutoRadius`, CS25 `…ofRSBreakdownCS25` (capacity-side ε_ca=1),
  KK25 `…ofLowerCapacityBCHKS25KK25`, DG25 `…ofSamplingDG25`.

────────────────────────────────────────────────────────────────────────────────
## §2.5  LIVE ATTACK ROUTES  (freshest in-progress machinery — the actual frontier)
────────────────────────────────────────────────────────────────────────────────
Three routes from the latest literature connect the LD challenge to the MCA challenge (solve
one ⟹ solve both). Each is mostly built in-tree; its GAP is the one open piece to attack.

**(R1) GG25 curve-decodability ⟹ MCA** (Guruswami–Gabizon, ePrint 2025/2054).
  · `ProximityGap.CurveDecodable C ℓ δ a b` / `MarkedCurveDecodable` — a degree-`ℓ` curve
    through `a` close points explains `≥ b` of them. (`GG25CurveDecodability`, `GG25MarkedCurve`.)
  · `GG25Lemma32.disagree_spread_bound` (Lemma 3.2) + `GG25MCAFromCurveDecodability`
    (`all_seeds_relClose`) — **curve-decodability ⟹ MCA (Thm 3.3), DONE** modulo the input.
  · **GAP:** GG25 proves curve-decodability only for FRS / multiplicity / random RS (field
    LINEAR in `n`), NOT explicit plain RS (the prize). Plain-RS curve-decodability is open.

**(R2) CZ25 subspace-design list-recovery** (the GG25 §4.3 curve-decodability argument).
  · `ProximityGap.exists_determining_tuple` — a tuple `v ⊆ T` whose coordinates **determine**
    a dim-`≤ r` list span `H`, when design param `θ < θ' = 1−δ`. Axiom-clean (`SubspaceDesignLineDecodable`).
  · `SeparationSurvivalCount.card_surv_ge` — combined separation + agreement count.
  · **GAP:** needs the list-recovery input `CZ25CoordFiberCap` (the `δ`-close codewords span dim `≤ r`).

**(R3) GM-MDS / Lovett higher-order MDS ⟸ δ*** (Lovett arXiv:1803.02523, AGL24).
  · `ArkLib/Data/CodingTheory/GMMDS/Lovett*` (10+ files) — the chain `δ* ⟸ L(δ) ⟸ higher-order
    MDS` reduces to the last residual `AGL24.GMMDSDualZeroPatternTheorem` (dual zero pattern).
  · **GAP:** the dual-zero-pattern theorem.

**(R4) The SYMMETRIC-FUNCTION / coset-rigidity route — the direct far-line incidence, reduced.**
  The far-line incidence is `Z/n`-dilation-invariant, so the extremal directions are monomials
  `X^a` (`FarLineIncidenceEquivariance`); the subgroup directions `X^{n/2}` are CORRELATED and
  discarded (`MonomialSubgroupCorrelated.lean`: `X^{n/2}=±1` on `μ_n`; jointly close on `μ_{n/2}`).
  For a NON-correlated direction `(X^a, X^b)`, working `mod m_S = ∏_{x∈S}(X−x)` (`S` the agreement
  set, `|S| = w = (1−δ)n`) the residues `X^{w−1+j} mod m_S` have complete-homogeneous-symmetric
  coefficients, so the bad scalar is a fixed symmetric function `γ = σ(e_•(S))` under vanishing
  of further symmetric functions of `S`. CLEANEST case `dir(k+1,k+2)`, `w=k+2` (PROVEN reduction,
  `probe_symmetric_function_reduction.py`, verified vs exact list-decode):
    `B = { −e_1(S) : S ⊆ μ_n, |S| = k+2, e_2(S) = 0 }`.
  · **MEASURED (the prize-regime facts):** the worst non-correlated incidence is **q-INDEPENDENT**
    and **`O(n)`** (`dir(5,7)`: `64,72,40,40` over `q=97..353`; `dir(5,6)→n`), crossing the prize
    level `q·ε* = n` strictly **inside the window** `(1−√ρ, 1−ρ)` (between `δ=0.562` and `0.625`
    at `n=16,ρ=1/4`). The bad set is a union of `μ_{n'}` cosets (`n'=n/gcd(b−a,n)`).
  · **GAP (the conjecture to prove — beats W4):** the symmetric-function value set
    `{ σ(S) : S ⊆ μ_n, |S|=w, vanishing-symmetric constraints }` has **`O(1)` `μ_n`-cosets**, i.e.
    worst non-correlated incidence `≤ C·n`. This is a CONCRETE, **q-independent** cyclotomic
    symmetric-function statement — it does NOT route through the incomplete-Gauss-sum-over-`F_q`
    wall (W4); the `q`-independence (proven by `mca_badscalar_general`, `#bad ≤ C(n,w)`) makes the
    whole quantity finite combinatorial. Proving the `O(n)` coset bound + the incidence/`δ*`
    calibration (worst incidence `= n` at `δ = δ*`) closes the MCA prize directly. The dilation
    `γ_S ↦ g^{b−a}γ_S` forces the coset structure; the open content is the *rigidity* (why all
    consistent `S` collapse to `O(1)` cosets).

Each GAP is a candidate `YOUR CONJECTURE HERE`: a closed plain-RS curve-decodability bound (R1),
a closed `CZ25CoordFiberCap` list-recovery dim bound (R2), the dual-zero-pattern theorem (R3),
or the `O(n)` symmetric-function coset-rigidity bound (R4) — any one, proved in the prize regime
without residual, closes the prize via its bridge.

────────────────────────────────────────────────────────────────────────────────
## §3.  THE WALLS  (PROVEN dead ends — every accessible technique stops here)
────────────────────────────────────────────────────────────────────────────────
**(W1) Per-witness counting is PROVEN EXHAUSTED.** `deviation_ownership_card` caps ownership
  at `C(w−1,d+1)`; production `k=Θ(ρn)` (`r=Θ(n)`) needs ownership `e^{Θ(n)}` while the
  scheme caps at `r+1`. The δ* prize needs *a genuinely different counting surface* — none known.
**(W2) Energy is the wrong lever.** Open at exponent `2+o(1)` (hard `7/3` barrier); above
  `p^{2/3}` no nontrivial subgroup-energy bound exists; and the √-loss (W-chain above) caps
  any energy bound at sub-Johnson. `WeilRegimeClosure` "capacity" = LARP (supply ≠ incidence).
**(W3) Confluent-Stepanov `n^{2/3}`** (the energy route's sharp input) needs the `a`-mixing
  Wronskian rep-point multiplicity — explicit caps at order 2, moment-combination trivial,
  same-`a`/distinct-roots/2-relation all fail (5 angles). Multi-week, no separable entry brick.
**(W4) Weil/√q wall.** `|η_b| ≪ √q` is vacuous for `|G|<√q`; coordinate-pigeonhole incidence
  surface refuted (target is the low-weight-error syndrome *variety*, not a coordinate ball).
**(W5) The budget/supply route pins δ* but ONLY ABOVE the window — PROVEN.** The all-stack
  `allWitnessDom_epsMCA_le` (`iSup` over *every* word stack — a *different* counting surface than
  W1's per-witness one) composed with the KKH26 upper witness PINS `δ* = 1−r/2^μ`
  UNCONDITIONALLY for the bulk/low-degree range, no `CensusDomination`
  (`KKH26AllWitnessPin.kkh26_deltaStar_pin_allWitness`; the budget-below-supply arithmetic is
  discharged outright for all `r ≤ √(2^μ)` by `choose_bulk`, giving the infinite family
  `kkh26_deltaStar_pin_lowdegree`; concrete `δ*=3/4` at `kkh26_deltaStar_pin_allWitness`'s
  `deltaStar_pin_concrete_F4129`; all axiom-clean). BUT this pins `δ*` at `ε* = supply/p`, and
  `1−r/2^μ = 1−ρ−Θ(2^{−μ})` sits in the near-capacity strip `(1−ρ−Θ(1/log n), 1−ρ)` — STRICTLY
  ABOVE the window-upper `1−ρ−Θ(1/log n)` for *every* `(μ,r)` (verified `in-win? = False`,
  `scripts/probes/probe_deltastar_window_calibration.py`). So the budget/supply machinery, though
  unconditional and general, structurally CANNOT reach the window interior: the prize `ε*=2^{−128}`
  is a *different, smaller* point on the `δ*(ε*)` curve where the line–ball incidence must be
  *sub-exponential* (= the open W4 incidence / incomplete-Gauss-sum problem). Do not expect a
  sharper budget/supply count to win the prize — it provably pins the wrong point.

────────────────────────────────────────────────────────────────────────────────
## §4.  WHAT A WINNING CONJECTURE MUST DO  (the closure contract)
────────────────────────────────────────────────────────────────────────────────
1. Give a **single computable** `δ*(ρ, ε*, n)` (or an `ε_mca(RS,δ)` bound) — no `∃`-over-
   incomputable objects, no named residual, no further open lemma.
2. Hold in the **prize regime** (constant `ρ`, `k=Θ(n)`, `q≈n·2^128`) — verify it does NOT
   collapse to Johnson (`1−√ρ`) or to the constant-DIM capacity result (`interiorCeiling_march`).
3. Beat the per-witness wall (W1): the incidence bound must NOT route through per-witness
   subset ownership (proven `e^{Θ(n)}`-short). It needs a new counting surface.
4. Be **machine-checkable**: instantiate at one concrete prize-shaped RS code and `decide`/
   prove the bound, then prove the general statement.

Once proved, wire it to `mcaConjecture` (T1) or a `GrandMCAResolution` (T2), then to the LD
prize via the GG25 curve-decodability bridge (T3).

────────────────────────────────────────────────────────────────────────────────
## §R.  RESEARCH SYNTHESIS 2026-06-13 — the two challenges collapse to ONE δ*, and
##      every published route provably misses the prize regime (plain RS, s=1).
##      (full map: `docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md`)
────────────────────────────────────────────────────────────────────────────────
**THE REDUCTION (defensible, from the ABF26 bridges).** The grand MCA challenge and the grand
list-decoding challenge share the *same* `δ*`:
  · MCA ⟹ list  (ABF26 Thm 5.2 [BCHKS25 1.9] / Thm 5.3 [CS25 2]): `ε_mca ≤ ε*` ⟹ `|Λ| ≲ ε*·|F|`.
  · list ⟹ MCA  (ABF26 Thm 5.1 [GCXK25 3]): `|Λ(C,δ)| ≤ L` ⟹ `ε_mca(C, 1−√(1−δ+η)) ≤ L²δn/(η|F|)`.
With `ε*=2⁻¹²⁸`, `q≈n·2¹²⁸`, so `ε*·|F| ≈ n`, hence the prize core is exactly:

  **`δ*_prize = sup{ δ : |Λ(RS[F, μ_n, k], δ)| ≤ ε*·|F| ≈ n }`**  — the radius where the
  *worst-case list size of explicit smooth-domain RS* crosses `~n`. Pin THIS and both fall.

**THE THREE PUBLISHED ROUTES AND THEIR FATAL GAPS (exhaustive — none reaches plain RS, s=1):**
  1. **List⇒CA** (GCXK25 Thm 3): has a **√-loss in the radius** (`δ → 1−√(1−δ)`) that ABF26 proves
     is FALSE to remove in general (Thm 5.4 [BGKS20] counterexample). OUT unless smooth structure.
  2. **Subspace-design / line-stitching** (JLR26 = arXiv 2601.10047 / GG25 = 2025/2054): proves
     `ε_mca ≤ (C₁/q)(n/η+1/η³)` up to capacity δ=1−R−η, BUT is **FRS-only** — needs folding
     `m=Ω(η⁻²)`; plain RS (`s=1`) has `τ(r)=R+O(r)`, useless. Its lemma chain is ~70% in-tree:
     Claim 5.8 = `subspaceDesign_list_dim_bound`, Lemma 5.4 = `curve_agreement_card_le` (both
     landed), Def 4.3 = `IsSubspaceDesign`, Lemma 5.5 = `exists_separating_*` (fleet); only line
     stitching (5.7) + peeling (5.10) remain — relevant for the FRS arm, NOT the prize.
  3. **Syndrome-space + witness reduction** (Yuan–Zhu arXiv 2605.07595, May 2026): `ρ<1−R−ε`
     up to capacity WITHOUT list decoding — but **random linear codes only** (random parity-check
     model); it works precisely because the random syndrome avoids `μ_n`'s additive structure.

**THE SINGLE NAMED OPEN TARGET (the prize core, no open-ended search).** Transferring route 3 to
explicit `μ_n` is the **line–ball incidence in syndrome space** (face iv, `epsMCA_ge_far_incidence`):
the bad-scalar count is `max over far-direction lines |{γ : syn(u₀)+γ·syn(u₁) ∈ B_{⌊δn⌋}}|`, where
`B_w` is the weight-`w` syndrome ball = high-frequency DFT image of weight-`≤w` errors over `μ_n`.
Pinning `δ*` is bounding this incidence; the controlling quantity is the **additive-energy / Sidon
structure of `μ_n`** (the in-tree energy + this-session antipodal work). A winning closed conjecture
states `max-incidence(δ) ≤ f(n,ρ,δ)` in closed form, with `f` crossing `n` at the claimed `δ*`, and
respecting the near-capacity lower bound `ε_mca ≥ n^{Ω(1)}/|F|` (ABF26 Table 1). This is the
`▼ YOUR CONJECTURE HERE ▼` slot's precise target — a syndrome line–ball incidence bound for `μ_n`.
-/

set_option linter.unusedSectionVars false
-- the prize objects (mcaDeltaStar, choose-budget) are heavy to elaborate; give a solver room:
set_option maxHeartbeats 1000000

namespace ProximityGap.Workbench

open scoped NNReal ENNReal
open ProximityGap ProximityGap.GrandChallenges
open ArkLib.ProximityGap.KKH26  -- evalCode: the explicit smooth RS code object used by the §2.4 pins
-- Substrate namespaces — every §2 lemma is now directly accessible by its short name:
open ProximityGap.MCAThresholdLedger      -- mcaDeltaStar, le_mcaDeltaStar_of_good, mcaDeltaStar_le_of_bad
open ProximityGap.FarCosetExplosion       -- epsMCA_ge_far_incidence (the law's engine)
open ProximityGap.SpikeFloor              -- mcaDeltaStar_rs_eq_granularity (the ladder)
open ArkLib.ProximityGap.KKH26CeilingMarch          -- interiorCeiling_march, march_badScalars_card_mul_le
open ArkLib.ProximityGap.OwnershipCensus            -- sharpened_*, deviation_ownership_card (the CEILING)
open ArkLib.ProximityGap.AdditiveEnergyRepBound     -- GVRepBound, additiveEnergy_cube_le_of_gvRepBound
open ProximityGap.BoundarySupExactness    -- rs_boundary_epsMCA_eq (the boundary n/q law)

/-! ## SMOKE TEST — every §2 substrate lemma resolves here (the "good experience" check).
If any `#check` below errors, the workbench is missing an import/open and must be fixed before
a solver relies on it. -/

-- §1 targets
#check @mcaConjecture
#check @GrandChallenges.mcaPrize
#check @GrandChallenges.mcaConjectureBound
#check @GrandChallenges.nonempty_mcaLowerWitness_of_mcaConjecture   -- conjecture ⟹ prize witness
-- §2 the law
#check @mcaDeltaStar
#check @le_mcaDeltaStar_of_good
#check @mcaDeltaStar_le_of_bad
#check @epsMCA_ge_far_incidence
-- §2 capacity-for-constant-DIM (the template, not the prize)
#check @interiorCeiling_march
#check @march_badScalars_card_mul_le
-- §2 granularity + boundary exact laws
#check @mcaDeltaStar_rs_eq_granularity
#check @rs_boundary_epsMCA_eq
-- §2 ownership bracket (W1: the proven-exhausted surface)
#check @sharpened_badScalars_card_mul_choose_le
#check @deviation_ownership_card
-- §2 energy / sub-Johnson list chain (W2/W3: the √-loss-capped route)
#check @additiveEnergy_cube_le_of_gvRepBound
-- §2 paper-bound witness bridges
#check @MCALowerWitness.ofJohnsonBCHKS25
#check @MCAUpperWitness.ofRSBreakdownCS25
-- §2.5 live LD⇒MCA routes (the frontier)
#check @CurveDecodable
#check @MarkedCurveDecodable
#check @exists_determining_tuple

/-! ## Sanity handles — the target objects are in scope and usable.

These trivial `example`s confirm the prize objects elaborate here, so a solver can write the
real statement directly against them. (They are not the prize; they certify the workbench.) -/

/-- The uniform MCA conjecture is the named target `Prop`. -/
example : Prop := mcaConjecture

/-- The MCA prize (all four rates, `ε* = 2^-128`) is in scope for any smooth domain. -/
example {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (domain : ι ↪ F) : Prop :=
  GrandChallenges.mcaPrize domain

/-- The operational threshold `mcaDeltaStar` is in scope (the law's δ*). -/
noncomputable example {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (C : Set (Fin n → F)) (εstar : ℝ≥0∞) : ℝ≥0 :=
  MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C εstar

/-! ════════════════════════════════════════════════════════════════════════════
    ║                     ▼▼▼   YOUR CONJECTURE HERE   ▼▼▼                       ║
    ════════════════════════════════════════════════════════════════════════════

    State the closed-form `δ*(ρ, ε*, n)` (or the `ε_mca` bound), prove it in the
    prize regime, beat the per-witness wall (W1), and wire it to `mcaConjecture`
    (T1) / a `GrandMCAResolution` (T2) / the LD prize (T3). Keep it CLOSED — no
    residual, no incomputable lemma. Prove a concrete prize-shaped instance first,
    then the general statement.

    Example skeletons (uncomment, replace `sorry` — but the prize needs NO sorry):

      -- def prizeDeltaStar (ρ : ℝ≥0) (n : ℕ) : ℝ≥0 := …            -- the closed form
      -- theorem prize_mcaConjecture : mcaConjecture := …            -- T1
      -- def prizeResolution … : GrandMCAResolution C epsStar := …   -- T2

    ════════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════════
    ║   §3   THE SHAW OPERATOR — the closed Proximity-Prize conjecture           ║
    ════════════════════════════════════════════════════════════════════════════

    UNIFICATION (proven, axiom-clean, `ProximityGap.ShawOperator`).  Every reduction of the prize
    δ* — the residual `(R) = worst − average`, the higher-order-MDS failure-correction `κ_d`, the
    off-diagonal spectral error of the line–ball incidence operator, the worst-case incomplete
    character sum `max|η_b|`, the higher additive energies `E_r` — is **one** quantity, the

        **Shaw operator**   `𝒮(S; s₀, s₁) = Σ_{ψ≠0, ψ⊥s₁} Σ_{s∈S} ψ(s₀−s)`

    (`ShawOperator.shawError`), the off-trivial spectral error of the line–ball incidence.

    SOLVE FOR δ* (proven, axiom-clean).  `ShawOperator.incidence_eq_average_add_shaw`:

        `#{γ : s₀+γ·s₁ ∈ S} · |V|  =  |F| · (|S| + 𝒮)`     — incidence = average + Shaw, EXACTLY.

    Since `δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger.mcaDeltaStar`), δ*
    is a *closed function* of the worst-case Shaw operator.  `incidence_pinned_of_shawBound` turns a
    Shaw budget into two-sided control of the incidence with **no open residual**.

    THE CLOSED CONJECTURE (the single open input).  `ShawOperator.MCAShawConjecture S B`:

        `∀ s₀ s₁,  ‖𝒮(S; s₀, s₁)‖ ≤ B`.

    With the prize budget `B = q·ε*·|V|/|F| − |S|` on the explicit smooth-domain δ-ball this is
    EXACTLY δ* reaching the prize window.  It is irreducible: NOT Johnson (the average term is
    strictly capacity-side), NOT a Weil/Parseval bound (W4-weak on `s₁^⊥` for `n ≪ √q`).  This is a
    closed bound on a single named operator — no residual, no incomputable lemma.  Proving it (the
    cyclic block-diagonal `Z/n` per-frequency estimate of `FarLineIncidenceEquivariance`) is the
    whole prize. -/

end ProximityGap.Workbench
