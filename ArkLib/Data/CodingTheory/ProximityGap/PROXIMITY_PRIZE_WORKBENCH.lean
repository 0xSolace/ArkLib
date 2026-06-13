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
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.Workbench

open scoped NNReal ENNReal
open ProximityGap ProximityGap.GrandChallenges
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

end ProximityGap.Workbench
