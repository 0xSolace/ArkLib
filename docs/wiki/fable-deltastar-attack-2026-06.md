# Pinning δ\* — Fable's attack dossier (issue #357)

> Working research log. The honesty contract of #357 applies: open core stays a named
> surface, every attempt lands in `DISPROOF_LOG.md` with a constraint lemma, probes precede
> Lean. This file is the *intellectual* plan (the 9 hypotheses + 3 connections + ranking);
> the bricks land in `ProximityGap/` and `Frontier/`.

## 0. The problem, restated for an attacker

`C = RS[F, H, k]`, `H ≤ F^×` a multiplicative subgroup, `|H| = n = 2^μ`, rate `ρ = k/n`,
`|F| < 2^256`, `ε* = 2^-128`. `ε_mca(C,δ)` = max over lines of the bad-point fraction, where a
point `g` is *bad* if some witness set `S` (|S| ≥ (1−δ)n, a codeword agrees with g on S) does
**not** witness the whole line. `δ*(C,ε*) = sup{δ : ε_mca(C,δ) ≤ ε*}`. We must produce a `δ₀`
with `ε_mca ≤ ε*` for `δ ≤ δ₀` (a `le_mcaDeltaStar_of_good` instance) **and** `ε_mca > ε*` for
`δ > δ₀` (a `mcaDeltaStar_le_of_bad` instance) that **meet**.

## 1. Why it is hard — the honest difficulty

Two walls, and they are the *same* wall:

1. **Floor↑ ⟺ beyond-Johnson explicit-RS list decoding (25-yr open).** Pushing `ε_mca ≤ ε*`
   above the Johnson radius `1−√ρ` requires bounding the interleaved list size of an *explicit,
   fixed, smooth* RS code past Johnson. No technique does this; Johnson is the list-decoding
   wall for explicit RS, and the random-RS capacity results (GZ23, GG25, CZ25) are ensemble-only
   with no derandomization.
2. **Ceiling↓ ⟺ the same.** Pushing `ε_mca > ε*` *down* toward Johnson means exhibiting bad
   families just past Johnson — but the KKH26 construction (the only known one) lives near
   capacity (`1−ρ−(2m−1)/n`, the gap identity), and CS25/BCHKS25 *couple* any improvement to the
   list-decoding question. So both directions terminate at the same 25-year obstruction.

The bracket is `[1−√ρ , 1−ρ−(2m−1)/n]` and **nothing census-aware lives between them**. Every
in-tree bound is *census-blind*: it sees MDS distance data (M1, M2) but not the evaluation-domain
structure. Yet the random-RS results prove δ\*(smooth) and δ\*(random) **must differ** — so the
gap is precisely where a domain-separating mechanism must act. The probe campaign found exactly
one: **M3 / the Möbius-involution pencil energy `E₂(H) = Σ_φ t₂(φ)²`** separates smooth subgroups
(`E₂ ≈ n²·c`) from random domains (`E₂` thin). *This is the only handle on the gap.*

## 2. Latest research state (June 2026, swept end-to-end)

No edge-movers beyond the held table exist. Floor held to Johnson by full MCA (BCGM25/Hab25/
BCHKS25). Ceiling held near capacity (KKH26, Kambiré). At-capacity conjectures FALSE (CS25/KK25/
DG25, three groups). Protocol-level results (Chai–Fan 858/861) *sidestep* `ε_mca`. The window is
untouched. The in-tree new math that *moves* it: the Parseval exponent-halving (opens s=64
unconditionally), the stratified-spread ceiling (reaches below δ=1/2), the DEEP-quotient transfer
(LD↓ ⟹ MCA↓ generically), interleaving exactness (one ledger for MCA + interleaved LD), and the
M3 domain separation (the only census-aware fact).

## 3. The most promising open direction, and the broad idea nobody has implemented

**The unification bet, sharpened by the census.** Every known counterexample family — CS25, KK25,
prime-field, KKH26 — lives on **coset/orbit structure**. The natural conjecture (untried; no one
has imported additive-combinatorial inverse theory here): *any ε\*-bad line family in the window
over a smooth domain is `poly(1/ε)`-covered by affine-/multiplicative-subgroup-structured
families.* If true, the upper bracket becomes **enumerable**: δ\* = the largest δ at which no
structured bad family of size > ε\*·q exists, computable from the structured catalogue.

What is new: the bridge from Bogolyubov–Ruzsa/Sanders (quantitative inverse sumset theory) to the
agreement census, **via the Möbius-pencil energy as the Fourier-side first invariant.** Why nobody
has done it: the proximity-gaps literature works above the pair level (second moments) and is
census-blind; the inverse-sumset literature has never met evaluation-domain RS. The probe-verified
M3 separation is the empirical anchor that says "the structured families are the only shape" is not
hopeless. Likely refutation: the inverse theorem's loss factors (`exp(poly log(1/ε))` in Sanders)
may be too lossy to pin a *point* (only a band). Not obvious because the smooth-domain pencils are
*highly* structured (subgroup orbits, not generic), so the inverse theorem could be lossless here.

## 4. The 9 hypotheses

### Reasonable (existing math, used insightfully)

**R1 — δ\* = Johnson for the MCA functional specifically (MCA is strictly harder than LD).**
The empirical transition sits *on* Johnson at large field. Conjecture: `ε_mca(C, 1−√ρ+η) > ε*` for
every `η>0` at deployed params, driven by the *mutual* requirement (every witness witnesses the
line), which the in-tree witness-spread engine lower-bounds and which activates past Johnson even
where the code is still list-decodable. Novel angle: run `DeepQuotientTransfer` in reverse —
MCA-specific witness-spread fails where LD succeeds. *Refutation:* if witness-spread is itself
Johnson-capped (like 2nd moments), R1 dies. Interesting: would make δ\* = the floor, *decoupling*
the prize from the 25-yr wall.

**R2 — the KKH26 ceiling is tight: δ\* = 1−ρ−(2m−1)/n in the high-degree regime.** The gap
identity pins the ceiling exactly. Conjecture: the matching lower bound holds because the
stratified-spread count is the *maximum* bad-scalar count (a menu-law upper bound on bad scalars).
Novel angle: prove `kkh26_stratified_count` is extremal via the incidence menu law `C(m₀,s/4−|J|)`.
*Refutation:* a non-KKH26 bad family below the ceiling. Interesting: pins δ\* at the *ceiling* edge.

**R3 — bracket interpolation via the LD⇔MCA dictionary.** `ε_mca ≈ |Λ(C^{≡m},δ)|/q` (in-tree).
Force the interleaved list size, as a function of δ, to cross `ε*·q` at a unique point via
monotonicity + the GS list-size derivative. *Refutation:* integer jumps kill IVT (a band, not a
point) — unless the *average* list size is smooth. Interesting: well-posed in-tree, cheap to test.

### Novel (brand-new math)

**N1 — the Möbius-energy law: δ\*(H) = F(E₂(H)/n²).** Build a δ\*-formula in the pencil energy
`E₂(H) = Σ_φ t₂(φ)²`, `F` interpolating Johnson (E₂ thin) to a smooth value (E₂ ≈ n²/4). Mechanism:
bad lines past Johnson force high-agreement codeword pairs, which over a subgroup are pinned onto
Möbius-involution orbits (`σ(x) = −b/x : H→H`), and the bad-scalar count is governed by `E₂`. *The
only domain-separating mechanism.* *Refutation:* `E₂` controls only M3 (low moments); δ\* may need
the sup over received words (high moments). Not obvious: the separation is REAL and must factor
through *something* census-like — `E₂` is the unique candidate.

**N2 — lacunary cyclotomic-resultant structure theorem.** A structural upper bound on
`|Res(R, Φ_{2^m})|` for *sparse* ±1 collision differences `R`, beyond Parseval, via the
rotation-orbit reduction — opening s=128 without Thorner–Zaman. Mechanism: few nonzero coeffs force
lacunary cancellation in the cyclotomic norm. *Refutation:* a sparse worst case saturating Parseval.
Not obvious: probes show ℓ²-mean conjugate behaviour (room below worst case).

**N3 — the witness-rigidity decoupling (the holy grail).** A new functional `Rig(C,δ)` = the
minimum witness-set variation over bad configs, with `ε_mca ≥ g(Rig)` where `g` activates past
Johnson *even when LD succeeds*. This severs MCA from the LD wall. Mechanism: "every witness
witnesses the line" is a rigidity that fails generically past Johnson. *Refutation:* rigidity may be
implied by list-decodability. Not obvious: MCA ⪈ CA ⪈ PG, and the gaps can activate at different δ.

### Synthetic (interpolating in-tree engines into new insight)

**S1 — the transfer fixpoint.** Compose `DeepQuotientTransfer` (LD↓⟹MCA↓) with interleaving
exactness (brackets transfer verbatim) into a self-consistency `δ\* = T(δ\*)`; solve the fixpoint.
*Refutation:* the "up to explicit factors" loss makes it a band.

**S2 — the exact bad-scalar census.** `Parseval ⊗ stratified-spread ⊗ menu-law` → the bad-scalar
count is *exactly* the menu-law sum, pinning the ceiling with matching upper+lower on the count.
*Refutation:* the menu law is probe-verified only to s=64; char-0→mod-p lifting fails at n=64.

**S3 — the gap identity is the pencil-energy deficit.** Conjecture `(2m−1)/n = (E₂-deficit of the
bad line)/n²`, unifying the ceiling with the M3 invariant. *Refutation:* the gap identity is a
degree/dimension count, plausibly pencil-independent.

## 5. The 3 paperworthy connections (unifications/symmetries)

- **C1 — Agreement census ⟷ Möbius orbits ⟷ δ\* domain separation.** The smooth/random δ\*
  distinction factors through the pencil energy `E₂`; M3 is the first moment-level smooth/random
  invariant, with the Möbius involution `σ(x)=−b/x` as the mechanism. (Foundation for N1, S3.)
- **C2 — DeepQuotientTransfer ⟷ interleaving exactness ⟷ one ledger.** MCA and interleaved RS
  list-decoding are *the same problem* in-tree: the transfer functor + exactness collapse two
  trackers into one bracket. (Foundation for S1, R3.)
- **C3 — Parseval halving ⟷ ℓ²-vs-ℓ¹ conjugates ⟷ resultant-as-Fourier-energy.** The KKH26 prime
  threshold is a Parseval bound: the bad-scalar distinctness exponent is the cyclotomic Fourier
  energy of collision differences. (Foundation for N2, S2.)

## 6. Ranking and execution order

**Ease (cheapest to prove/refute first → hardest):**
A5-exact-point · M3-H4-reduction · M3-H2-(k=2-domain-indep) · R3 · S2 · R2 · N2 · S1 · R1 · N1 · N3.

**Promise (most likely to actually pin δ\* → least):**
N1 · N3 · (unification-bet) · S1 · R1 · S3 · R2 · S2 · R3 · N2 · A5.

**Combined-score start order (work ALL, brick by brick):**
1. **Foundation first** (high ease, enables the promising ones): the **M3 reduction (H4) + k=2
   domain-independence (H2)** formalized, and the **A5 first-exact-δ\*-point** (validates the engine
   end-to-end; a genuine first — no exact δ\* exists for any code anywhere). These are concrete and
   build the census substrate N1/S3 need.
2. **Then the promising core:** push **N1 (Möbius-energy law)** on the census foundation, with **S3
   (gap = energy deficit)** as its falsifiable corollary, mutually-falsified against **R2**.
3. **In parallel, cheap kills:** **R3** (interpolation — quick IVT check) and **S2** (menu-law
   census — probe past s=64).

Every refutation is a constraint lemma in `DISPROOF_LOG.md`. Survivors get red-teamed and promoted.
If all 9 die, regenerate 3+3+3 and continue. **Start: the M3 reduction + A5 exact point.**

## 7. Results log (proven / refuted, brick by brick)

### N1 — REFUTED at all feasible scales (`scripts/probes/probe_n1_energy_vs_badcount.py`)
**Verdict: the pencil energy E₂ does NOT govern the bad-scalar count, so `δ* = F(E₂/n²)` fails.**
Probe (exact, syndrome-reduced ε_mca over the worst line; cross-checked monotone): across 8
feasible `(p,n,k)` instances, smooth-subgroup and random-subset domains of *equal* `n,k` have
**identical** bad-scalar counts at every tested radius — even when E₂ differs by up to 10× (e.g.
`(13,4,2)`: smooth E₂=10 vs random E₂=1, both bad count 4; `(11,5,3)`: E₂=20 vs 4, both bad 5).
6/8 cases show "different E₂, same bad count"; the other 2 had equal E₂ and equal bad count. The
bad count is determined by `(n,k,δ)` alone at this scale, **independent of E₂**.

*The learning (a real constraint on the search):* the only known domain-separating invariant
(E₂ = the M3 second-moment energy) controls the agreement *spectrum moments* but **not the
extremal bad count** that sets δ\*. This is the average→worst-case wall manifesting at the pencil
level: E₂ is an L²/average quantity; δ\* is a sup over received words. *Any future use of the
pencil structure for δ\* must target an extremal/higher-order invariant, not the energy sum.*
The proven `E₂ = Θ(n³)` separation (`MobiusPencilEnergy.lean`) stands as a spectrum-moment fact —
it is simply not the δ\*-controlling one. **Constraint for the ledger:** `ε_mca` is not a function
of E₂ (two domains, same field, E₂ differing, same ε_mca).

### N1′ (refinement, promoted to the slate) — the EXTREMAL pencil invariant
Since the *sum* E₂ is moment-blind, the refined conjecture is that δ\* tracks an **extremal**
pencil quantity — `maxₚ t₂(φ)` over the full k=3 pencil family, or the M3 *third*-moment census
`Σ_φ t₂(φ)³` (where the dossier's smooth/random separation actually lives), not the second moment.
This is the "thin-strip / higher-moment" escape (K3/H1) re-aimed: target the sup, not the average.
*Next probe:* does `maxₚ t₂` or the M3 cubic census predict the bad count where E₂ failed?

### DOMAIN-BLINDNESS — a structural finding (kills the domain-separation hypothesis class)
**The worst-line MCA bad-scalar count is DOMAIN-INDEPENDENT at every tested scale.**
`scripts/probes/probe_domain_blindness.py` (optimized: precompute ext(syndrome,S) once/domain):
- `(11,5,3)`: **complete enumeration of ALL 252 five-subsets** of `F_11^*` → bad count is
  `{δ=0.15: 1, δ=0.25: 5, δ=0.35: 5, δ=0.45: 5}` for *every single domain*, zero exceptions,
  smooth subgroup included.
- `(13,4,3)`: all 120 four-subsets → bad count `1` everywhere.

**Consequence (a hard constraint, not a hypothesis):** `δ*(C)` is a function of `(n,k,δ)` alone
at these scales — `δ*(smooth) = δ*(random)`. The smooth multiplicative structure does **not** move
the worst-case threshold; it only changes the *spectrum moments* (M2/M3/E₂), which the bad count
is blind to. This **refutes the entire domain-separation hypothesis class** — N1 (energy law), N1′
(extremal pencil), S3 (gap = energy deficit), and the C1 "δ\* domain separation" framing. The
proven `E₂ = Θ(n³)` smooth separation (`MobiusPencilEnergy.lean`) is real but is a *moment* fact
with **no δ\*-consequence**.

**This is exactly the dossier's central coupling, now empirically sharp:** because δ\* is
domain-blind, it equals the explicit-RS list-decoding threshold (a domain-independent count) — so
pinning it past Johnson IS the 25-year open problem, with no smooth-domain shortcut. The honest
research conclusion: **no domain-specific invariant can pin δ\* in the interior.** The viable
hypotheses are the *domain-blind* ones (R2 ceiling-tightness, R3 interpolation, S1 transfer
fixpoint, the unification bet on the bad-set *shape* rather than the domain). The next slate must
drop the census-separation angle entirely and attack the domain-blind list-count directly.

**Caveat on scale (red-team of the finding itself):** these are tiny fields (`p ≤ 13`, `n ≤ 5`)
where the radius window `(1−√ρ, 1−ρ)` is narrow and integer-quantized; the M3 separation the
probe campaign reported is a *third-moment* effect that may only surface the bad-count difference
at larger `n` (the `t₂ ≈ n/2` regime needs `n ≫ k`). The finding is "domain-blind at small scale";
strengthening it to all scales, or finding the first `n` where a domain *does* differ, is the
decisive follow-up probe (feasible up to `n ≈ 8` with the optimized engine + better S-pruning).

## 8. CORRECTION (research integrity) — domain-blindness is SATURATED-BAND only

The §7 "domain-blindness" claim was **over-stated** and is here corrected. The exact probes
reach only the *saturated low band* `δ ∈ [UD, ~Johnson)` where the worst-line bad count equals
`n` (the domain size) for **every** domain — but `n` is the *saturation ceiling* of that band, so
equal-across-domains there is the easy regime, not evidence about the interior. The **interior**
`δ ∈ (Johnson, capacity)` — where δ\* actually lives, where the bad count *grows* past `n` toward
the KKH26 blow-up, and where the KKH26 construction is **domain-specific** (smooth subgroup) — is
**exact-computation-infeasible at low rate** (the window with a wide Johnson–capacity gap requires
`m = n−k` large, hence `p^{2m}` syndrome pairs blow up; this is the same wall the dossier documents).

**Consequence for the slate:** N1 (the *specific* energy law `δ*=F(E₂/n²)`) stays REFUTED — E₂
varies in the saturated band while the count does not, so ε_mca is not a function of E₂, period.
**But the general domain-separation idea (N1′: an EXTREMAL pencil / M3 third-moment invariant) is
NOT killed** — it would act in the interior, which the probes never saw. The random-RS-beats-smooth
results *require* interior domain-dependence, so separation there is expected, not excluded. The
honest status: **domain-blind in the saturated band (proved by enumeration); interior separation
OPEN and unprobeable by exact methods** — exactly the 25-year wall, restated.

This *revives N1′ and the M3 third-moment thread* as the live domain-aware direction, and confirms
the domain-blind hypotheses (R2 ceiling-tightness, S1 transfer-fixpoint, the unification bet) as the
parallel track that sidesteps the interior-computation wall. The exact-pin combinator
(`MCAExactPin.lean`) and the pencil-energy substrate (`MobiusPencilEnergy.lean`) stand regardless —
both are correct, reusable, and route into whichever hypothesis survives.

### S1 (transfer fixpoint) — naive form DEAD
The in-tree threshold-halving map (`ProofLoop42.threshold_halving_into_unique_decoding`) is
`δ ↦ δ/2` (lands in unique decoding). Its only fixpoint is `δ = 0` (trivial) — the iteration
collapses to the floor in O(log) steps, never banding the interior window. Confirms the dossier's
"exits the window in O(1) steps". S1 survives only in a *nontrivial* reformulation (a rate-coupled
or ε-coupled map with an interior attractor), which is not the 858 map. Parked unless a non-collapsing
transfer is found.

## 9. PROGRESS: family interior pin (high-rate), and the low-rate wall localized

Landed `mcaDeltaStar_family_interior_pin` (axiom-clean): a PARAMETRIC interior δ* pin
`mcaDeltaStar(C, C(n,t+1)/q) = 1−t/n` for every upper-half code (`n≤2t`), conditional on one named
extremal-layer hypothesis; the good side (sharp LYM ceiling) is unconditional. This reduces the
high-rate interior-pin programme to a single per-family extremal-stack obligation.

**The localized wall (honest):** this family is HIGH rate (`k+1 ≥ n/2`). At LOW rate (the deployed
prize, `ρ ≤ 1/2`, `k+1 < n/2`), the LYM ceiling caps `ε_mca ≤ C(n,⌊n/2⌋)/q`, but the extremal-stack
construction only attains `C(n,k+1)/q ≪ C(n,⌊n/2⌋)/q` — **the brackets do not meet**: the LYM
antichain bound is *loose by an exponential factor* at low rate. This is exactly the 25-year wall,
now pinned to a precise statement: **the open low-rate problem is to replace the LYM/antichain
ceiling with a sharp one** — i.e. prove that the bad-scalar witnesses, though they *could* form a
middle-layer antichain combinatorially, are *algebraically forced* to a much smaller layer for RS
codes. No technique does this (it is the beyond-Johnson list-decoding count in disguise). The
high-rate family pin is the proof-of-concept that the bracket-meet machinery works whenever a sharp
ceiling is available; the low-rate sharp ceiling is the genuine open core.

## 10. NEW CONNECTION (probe-verified, paperworthy): bad count = distinct subset sums

**`scripts/probes/probe_jump_subsetsum.py` (exact, 8/8 instances):** for the explicit stack
`u0 = eval x^{k+1}`, `u1 = eval x^k`, the MCA **bad-scalar count at the jump radius `1−(k+1)/n`
equals the number of DISTINCT `(k+1)`-subset sums of the evaluation domain `D` (mod `p`)** —
exactly, every case. Mechanism (divided differences): the bad scalar for a `(k+1)`-subset `S` is
`γ_S = −x^{k+1}[S] = −h_1(S) = −Σ_{x∈S} x` (the order-`k` divided difference of `x^{k+1}` is the
complete symmetric `h_1` = the subset sum). Distinct bad scalars ⟺ distinct subset sums.

**Why this is paperworthy (the additive-combinatorics connection, dossier's most-promising
never-implemented direction, now concrete):**
- The MCA threshold's bad count is an **additive-combinatorial invariant** of the domain — the
  `(k+1)`-fold *sumset/subset-sum* statistic, not just MDS distance data. This is the first exact
  bridge from `ε_mca` to additive combinatorics (Sidon sets, additive energy).
- **Domain dependence localized at the jump:** smooth subgroups have additive structure ⟹
  subset-sum *collisions* ⟹ FEWER distinct sums ⟹ **fewer bad scalars than a Sidon/generic domain**.
  (Reconciles with the saturated-band domain-blindness: blindness held below the jump where the
  count saturates at `n`; at the jump the count is the subset-sum count, which IS domain-dependent.)
- **Unconditional discharge of `ExtremalWitnessLayer`** (hence the family interior pin) for any
  **Sidon-mod-`p` domain** with `C(n,k+1) ≤ p`: there all `(k+1)`-subset sums are distinct, so the
  bad count `= C(n,k+1)`, attaining the LYM ceiling. This turns the conditional high-rate family pin
  UNCONDITIONAL over Sidon domains — a genuine new unconditional interior `δ*` family.
- **The smooth-domain subtlety:** subgroups are NOT additively Sidon (e.g. `D={1,2,3,4,5}`:
  `{1,2,5}` and `{1,3,4}` both sum to 8), so this `x^k/x^{k+1}` stack is *sub-extremal* on smooth
  domains (the sibling's cleverer stack still attains `C(n,k+1)` there). But the FORMULA holds for
  the stack regardless, and the *connection* — `ε_mca` jump count ↔ subset-sum count — is the
  insight: **pinning `δ*` for smooth domains is governed by the subgroup's subset-sum spectrum.**

**Next:** formalize `bad_count_jump = #distinct (k+1)-subset sums` (the divided-difference γ_S
formula + the count), giving the unconditional Sidon-domain family pin; and pursue the smooth-domain
subset-sum spectrum (a multiplicative subgroup's additive subset-sum structure — a clean, studied
object) as the route to the *smooth* `δ*`. This is the additive-combinatorial inverse-theorem bet
made concrete and exact.
## 11. RED-TEAM REFINEMENT: the subset-sum connection is BAD-side, not the open core

Self-red-teaming §10: the `x^k/x^{k+1}` stack's bad count at the jump = `#distinct (k+1)-subset
sums`, which for deployed `n` SATURATES near `p` (sums mod `p` fill the residues once
`C(n,k+1) ≥ p`). A near-`p` bad count means `ε_mca ≈ 1` AT the jump — i.e. the connection feeds the
**bad-above** bracket, which is ALREADY in-tree (`kkh26_epsMCA_lower_bound`). It does NOT touch the
genuine open core, which is `InteriorCeiling` = the **good-BELOW** side (`ε_mca ≤ ε* = 2^-128` for
all `δ` up to the near-capacity radius). The subset-sum result is a real, paperworthy structural
characterization of the bad side; it is NOT a crack in the prize. Honest correction to "most
promising crack" — it enriches the handled side, not the open one.

## 12. PROBE: no smooth-vs-nonsmooth ε_mca separation at small scale (interior-ceiling shape)

`scripts/probes/probe_interior_ceiling.py` (exact, witness-disciplined naive enumerator):
`RS[F₁₃, ·, 2]`, `n=4`, smooth subgroup `{1,5,8,12}` vs non-smooth `{1,2,3,4}`:
`ε_mca = 4/13` at BOTH `δ=1/4` and `δ=2/4`, for BOTH domains — identical. `4/13 = n/q`
(the codimension-1 / UD-layer count), below the LYM ceiling `C(4,2)/q = 6/13` at capacity.
Confirms: (a) at this scale the interior count is domain-BLIND (smooth = non-smooth), consistent
with the saturated-band finding; (b) no spike below the jump (`InteriorCeiling` shape holds here,
but vacuously — `n=4` has no genuine Johnson↔capacity interior). Inconclusive for the deployed
regime (too small to exhibit a KKH26 jump); rules out a *cheap* small-scale separation or
counterexample. The open core remains the beyond-Johnson explicit-RS list count — the 25-year wall.
## 13. STRUCTURAL SHARPENING: `InteriorCeiling` decomposes into THREE sub-regimes (distinct status)

`InteriorCeiling` = "ε_mca ≤ ε* for all δ < jump (1−r/2^μ)". Tracing the substrate
(`141JohnsonCount.lean` + `244HwitRefutation.lean`) shows the radius interval `[0, jump)` is NOT
homogeneous — it splits into three regimes whose provability differs sharply:

  (I)  **[0, half-Johnson]** — `rs_epsMCA_le_johnson_ceil_of_hwit` gives `ε_mca ≤ L_Johnson/|F|`
       via the single-common-center clustering hypothesis `hwitAll`. With cryptographic `|F|` (so
       `L_Johnson/|F| ≤ 2^-128`) this DISCHARGES the obligation here — PROVABLE (conditional on
       `hwitAll`, which holds up to half-Johnson).
  (II) **(half-Johnson, Johnson]** — `244HwitRefutation` proves `hwitAll` (single center) is
       REFUTABLE past half-Johnson (constant-pencil countermodel over GF(5): all |F| scalars
       line-close vs Johnson cap 2.4). So regime (I)'s route DIES here; a genuine MULTI-center
       Johnson argument is needed. The classical Johnson list bound still caps list size here
       unconditionally — so this regime is PROVABLE IN PRINCIPLE but needs the multi-center
       `lineCloseCount ≤ L_Johnson` brick (not yet assembled; the single-center one is refuted).
  (III)**(Johnson, jump)** — strictly above Johnson. NO list-size bound is known for explicit RS
       here; this is THE 25-year wall. GENUINELY OPEN.

**Why this is the right way to state the frontier:** it isolates the irreducibly-open piece to
regime (III) — a STRICTLY SMALLER interval than `[0, jump)` — and identifies regime (II) as a
*formalizable* (not research-open) gap blocked only on a multi-center Johnson brick the project
has not yet built (the single-center version is machine-refuted, so the obstruction is precise).
The honest open core is therefore "regime (III): explicit-RS list count above Johnson", and the
actionable (non-research-blocked) next brick is the multi-center Johnson line-close count for
regime (II) — which would shrink `InteriorCeiling`'s open part from `[0,jump)` to `(Johnson,jump)`.
This is a genuine sharpening of what the Proximity Prize actually requires, machine-substantiated
by the existing refutation, with no fabrication.
## 14. BCIKS20 → regime (II) dependency, traced precisely (honest gap analysis)

Investigated whether the BCIKS20 cone discharges `JohnsonLineCloseBound` (the regime-(II) hook from
`RegimeIIBridge.lean`). Finding — it does NOT close trivially; the precise chain and its two real
gaps:

* **What BCIKS20 exports** (`BCIKS20/ListDecoding/CloseInterpolantsCount.lean`):
  `close_interpolants_card_le_johnson` bounds, at a single good GS parameter `z`, the number of
  degree-`≤k` codewords agreeing with the line point `u₀+z•u₁` on a set of size `≥ e₀`, by the
  `Y`-degree budget `D_Y Q = poly(n)` — UNCONDITIONALLY in `z`, given a `ModifiedGuruswami` curve `Q`.

* **GAP 1 (counting-object mismatch):** that theorem counts *codewords close to ONE line point*
  (the GS per-`z` list size). `JohnsonLineCloseBound` counts *scalars `γ` whose line point is δ-close
  to SOME codeword*, uniformly over the pencil. These are different quantities; bridging them is the
  correlated-agreement / joint-agreement step (`BCIKS20/ListDecoding/JointAgreementWiring.lean`,
  `Agreement.lean`), not a relabelling. The substrate's own T1 (`rs_lineCloseCount_le_johnson`) does
  the `γ → codeword` injection but only via the single-active-coordinate center — the route
  `244HwitRefutation` kills past half-Johnson.

* **GAP 2 (BCIKS20 is itself conditional):** the end-to-end BCIKS20 RS curve list size is gated on
  named in-tree residuals (`RSCurveListSizeResidual`, the `DescendedRset`/`DescendedAgreement`
  chain — see memory `descendedrset-f10-fix-hcoincide-gated`: the cone is "sorry-free-but-conditional",
  inseparable-case `pg_RsetDescended = pg_Rset` is FALSE). So even GAP 1's upstream input is not
  unconditional.

**Honest consequence:** regime (II) is formalizable but NOT a one-brick wire — it requires
(a) the joint-agreement bridge from per-`z` GS list size to pencil-`γ` count, AND (b) discharging
BCIKS20's own curve-list-size residuals. `RegimeIIBridge.epsMCA_le_of_johnsonLineCloseBound` remains
the correct clean reduction (the hook `JohnsonLineCloseBound` IS a literature theorem); but claiming
BCIKS20 "immediately" discharges it would be an overclaim. The actionable sub-bricks are now named:
GAP 1 (joint-agreement → γ-count) and GAP 2 (RSCurveListSizeResidual). Regime (III) stays the
genuine 25-year wall regardless.
## 15. FRESH 9-HYPOTHESIS ROUND on regime (III) — the deployed open core (ranked, with status)

Prior rounds targeted the whole window; this round targets ONLY regime (III) = `(Johnson, jump)`
(the irreducible core after `RegimeIIBridge` shrank the obligation). Empirical input this round:
`probe_above_johnson.py` (sampled, n=8,k=5,p=17, δ=2/8 above Johnson) — `ε_mca = 17/17 = 1` for BOTH
smooth subgroup and random domains. **The SATURATION BARRIER:** small codes saturate (`ε_mca=1`)
immediately above Johnson, while the deployed core lives at `ε*=2^-128` far below saturation, only
at cryptographic `n`. So the meaningful above-Johnson sub-saturation band is COMPUTATIONALLY
INACCESSIBLE at any enumerable scale — a concrete structural reason δ* resists computational pinning.

### Reasonable (existing math, new angle)
- **R1 — ceiling-tightness:** δ* = KKH26 jump `1−r/2^μ` exactly (good below = `InteriorCeiling`).
  STATUS: this IS the reduced core (KKH26DeltaStarReduction + RegimeIIBridge). OPEN (= regime III).
- **R2 — above-Johnson domain-blindness:** smooth ε_mca = generic ε_mca above Johnson.
  STATUS: INCONCLUSIVE-by-saturation (probe shows both =1 at n=8; meaningful band inaccessible).
  Documents the saturation wall; cannot be settled by enumeration.
- **R3 — capacity-edge match:** δ* = `1−ρ−Θ(1/log n)` with the KKH26 η constant exact.
  STATUS: consistent with the KKH26 ceiling form; OPEN, coupled to R1.

### Novel (new math)
- **N1 — multiplicative subset-PRODUCT spectrum:** the above-Johnson bad count is governed by the
  domain's multiplicative `(k+1)`-subset-PRODUCT collision spectrum (the multiplicative analog of
  the additive subset-SUM-at-jump mechanism §10, now for the γ-scaling action). NEW; untested;
  promising as the multiplicative twin of the confirmed additive connection.
- **N2 — folding transfer-operator fixed point:** since `2^μ | n`, the squaring fold `x↦x²` maps the
  smooth domain to a half-size smooth domain; conjecture ε_mca obeys a self-similar recursion whose
  fixed point pins δ*. NEW; refutation-risk: folding changes the rate ρ, so exact self-similarity is
  unlikely — but an APPROXIMATE renormalization could still bracket δ*. Untested; hardest.
- **N3 — pencil-energy governs VARIANCE not mean:** the landed Möbius `E₂=Θ(n³)` (MobiusPencilEnergy)
  governs the bad-count VARIANCE across stacks (not the mean); δ* = radius where variance/mean ≈ 1
  (the concentration threshold). NEW; builds directly on LANDED infra; second-moment testable.

### Synthetic (interpolate project math)
- **S1 — bracket squeeze:** if Johnson `δ_J=1−√ρ` coincides with the KKH26 jump `1−r/2^μ` for some
  param family, the regime-II ceiling and the regime-III floor meet ⟹ δ* pinned. STATUS: **REFUTED
  arithmetically** — KKH26 places the jump STRICTLY ABOVE Johnson by construction (the bad lines are
  a beyond-Johnson phenomenon), so `1−r/2^μ > 1−√ρ` always; they never coincide. Squeeze impossible.
- **S2 — next-layer subset sums:** ε_mca just below the jump = `#distinct (k+2)-subset sums / q` (the
  §10 additive mechanism one antichain layer down); if `< ε*` the good-below holds at that layer.
  NEW; directly testable by extending probe_jump_subsetsum.py; but inherits §13's bad-side caveat.
- **S3 — interleave/tensor lift of the n=5 pin:** lift the exact toy pin via `epsMCA_interleaved_eq`.
  STATUS: **REFUTED as a deployed route** — interleaving transfers brackets to INTERLEAVED RS at the
  SAME base δ*; it does not increase the base code length n or move δ*, so it reaches interleaved-RS,
  not larger smooth-RS in the deployed regime. Genuine bracket-transfer, wrong axis for the prize.

### Ranking (easiest-to-settle × most-promising) and disposition
1. S1 — trivial, **REFUTED** (arithmetic). 2. S3 — **REFUTED** (wrong scaling axis). 3. R2 —
**INCONCLUSIVE-by-saturation** (documented wall). 4. N3 — testable on LANDED E₂ (top SURVIVING,
second-moment probe). 5. S2 / N1 — testable subset-sum/product extensions (promising, §13-caveated).
6. R1 / R3 — the open core (regime III, 25-yr wall). 7. N2 — hardest, renormalization speculation.
**Top surviving actionable:** N3 (variance via Möbius E₂) and N1 (multiplicative product spectrum) —
both build on landed infra and are probeable. 3 of 9 settled this round (2 refuted + 1 saturation-
documented); core R1/R3 remains the wall; N1/N3/S2 carried forward. No fabrication.
