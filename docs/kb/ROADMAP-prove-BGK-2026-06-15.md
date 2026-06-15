# Roadmap to Prove BGK — the RS proximity-gap prize core (#444)

**Target.** `M(n) = max_{b≢0(p)} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m)`, `C=O(1)`, `μ_n` = 2^μ-th roots of unity
in `F_p`, `n=2^μ`, `p≈n^4` (Burgess barrier β=4), `m=(p−1)/n≈2^128`. Proving this is the prize.

Synthesized from the full #444 dossier (§6 live / §8 dead) + a digest of the 207 comments (the recent
"wf6/wf7" cluster, post-body-fold). Every load-bearing brick cited is present on `fork/main` and reported
axiom-clean; numeric claims are flagged. Honesty contract applies — the core is 25-year-open; this is a map
of *where* the single remaining input lives, not a closure.

---

## 0. The reframing that organizes everything (recent, decisive)

The prize is the **char-p validity, at depth `r ≈ log q ≈ 89`, of the deep-rung Wick bound**
`A_r = p·E_r(μ_n) − n^{2r} ≤ (2r−1)‼·n^r`. The char-0 version is **PROVEN for all r** (Lam–Leung antipodal;
`_CharZeroWickEnergy.gaussianEnergyBound_dyadic`). So **the entire open content is one transfer: char-0 → char-p,
at depth.** Three faces are now proven logically identical (`MomentWickBridge`, `_AR_HypercontractiveWickEquivalence`):
Wick-energy ⇔ metaplectic L²→L∞ amplification ⇔ the sub-Gaussian `L^{2r}/L²` constant `((2r−1)‼)^{1/2r}`.

**The single most important recent finding (W1, `_wf7W1_WickToGaussianMGF.lean`, comment 4711338050).**
The *right object* is the **DC-subtracted Gaussian MGF envelope**, not the per-coefficient Bessel bound:

> `Φ_p(y) := (1/q)·Σ_{b≠0} cosh(η_b·y) ≤ exp(n·y²/2)`, uniform in `y` (saddle `y*=√(2 log q/n)`).

- The **per-coefficient K=1 Bessel form** `Φ_p ≤ I₀(2y)^{n/2}` **FAILS** (ratio 1.0909 at n=128): the
  spurious mod-p excess `E_r(p) > E_r^{(0)}` is real at intermediate r.
- The **Gaussian envelope HOLDS uniformly** (ratio ≤ 1; 0.04–0.19 at the saddle, measured to **n=256**): the
  excess is *absorbed* by the Bessel→Gaussian slack. Bridge `mgf_le_exp_of_wick` (axiom-clean) turns a per-r
  K-Wick bound into exactly this envelope.

This is the strongest "prize-true" evidence yet on the correct object, and it tells us **what to prove**: the
aggregate MGF envelope, where per-coefficient failures cancel — not the per-r coefficients.

---

## 1. Ranked avenues

### #1 — char-p deep Wick / MGF envelope  ★ THE path (feasibility 6–7/10)
The clear leader: char-0 fully proven, numerics favorable to **n=256**, and reduced to a small set of
**equivalent** char-p cruxes (pick the easiest to prove; any one closes the prize). All are
b-sensitive + deterministic + genuinely-L∞ (pass the §4 necessary condition) because they live in the deep-r
moment, not a second-order object. The sub-targets, sharpest first:

| Sub-target | Statement (char-p crux; char-0 PROVEN) | Brick | Status |
|---|---|---|---|
| **W7 Newton-slope DC-dominance** | `Spur_r(p) := E_r(p)−E_r^{(0)} ≤ n^{2r}/p` (slope-≥1 (1−ζ_p)-adic mass ≤ the subtracted DC term) ⇒ `A_r≤Wick` with **K=1 exactly** | `_wf7W7_NewtonSlopeDCDominance.lean` (`wick_bound_K1_of_dc_dominance`) | pre-screened `GEN_r<0`, margin **grows** n≤64, β≤5 |
| **W3+F1 step-ratio / hypercontractive** | all-r Wick ⇐ one per-step `E_{r+1}≤(2r+1)·n·E_r` ⇐ `M_4≤3n·M_2` (finite base) **+** `StepRatioAntitone` (R(r) antitone = log-Sobolev/Bonami–Beckner content) | `_wf6F1_…`, `_wf7W3_HypercontractiveStepAntitone.lean` | telescope axiom-clean; **antitone is the open sign condition** |
| **F2/W5 dyadic cumulant descent** | `Cum(μ_n,r)=2·Cum(μ_{n/2},r)+q·Cross−(2^{2r}−2)|H|^{2r}` — last term **strictly negative** (the contractivity the dead magnitude-tower lacked); crux = per-level `RhoContractiveAtDepth` | `_wf6F2_…`, `_wf7W5_kstability_tower.lean` | descent + negative term PROVEN; K=1+o(1) to n=256 |
| **c_r≤1 single-monotonicity** | normalized recursion ⇒ one inequality `c_r≤1`; sharpened to per-r autocorrelation sup `max_{δ≠0} C_r(δ) ≤ 2r·Wick_r/(n−1)` | `CharPWickConditionalPin.lean`, `CharPWickAutocorrPin.lean` | recursion+base+consumer proven; crux open |
| **W6 geometry-of-numbers** | `Spur_r(p)=#{v∈L_p: v≠0, ‖v‖²≤φ(n)·2r}` (short vectors in index-p sublattice of ℤ[ζ_n], trace form, exact length `φ(n)·|T|`); crux = **counting-transference** (2nd-moment Minkowski/Banaszczyk) | `_wf7W6_shortvector_spur.lean` | λ₁-gap form REFUTED ⇒ genuinely needs the *count* |
| **Chebotarev arithmetic count** | `Spur_r(p)=#{antipodal-free T,|T|≤2r : p\|N(σ_T)}` — an arithmetic count; cuts: sum-of-two-squares (p≡3(4) ⇒ even power), density-`1/2^{m−1}` class p≡1(2^m), per-relation ceiling `p≤w^{2^{m−1}}` | `SpurBadPrimeChebotarev/Ceiling/ShortRelationNormBase.lean` | reduces to effective-Chebotarev splitting count |

**Honest catch (the recurring good-prime/bad-prime wall).** The proven char-p lift
`|Res(Φ_n,f)|² ≤ (2W)^{φ(n)}` discharges relations for `p > (2W)^{n/4} = 52^{n/4}` — **super-polynomial, exceeds
the prize prime.** So it's a *generic-prime* mechanism; the specific prize prime `≈2^160` must beat it. Every
sub-target above ultimately asks: control `Spur_r(p)` at the *single* prize prime at depth r~log q. That is the
one open input.

### #2 — Direct analytic-NT (Burgess/HBK/di Benedetto)  (feasibility 2/10, needs external)
Best proven: `n^{0.989}` (di Benedetto–Garaev), but its range needs `H>p^{1/4}` **strictly** — it **vanishes at
β=4**. The Burgess exponent infimum is exactly 1 at p^{1/4}. **Missing input:** an effective character-sum
cancellation for thin 2-power subgroups *at* the Burgess barrier — i.e. the Paley Graph Conjecture / a
subconvexity bound for the attached family. **Open, no known route.** Not independent — *is* the wall.

### #3 — Sum-product / energy (feasibility 2/10)
`E_+(μ_n)=3n²−3n` is at the **Sidon floor** (minimal) yet still doesn't cross — proving the barrier is **not
energy-size** but the **energy→character-sum transfer exponent**. Higher/asymmetric energies + proven incidence
(Rudnev–Stevens, BSG) don't change the transfer barrier. **Missing input:** a transfer that doesn't lose the
half-power. Reduces to the wall.

### #4 — Effective equidistribution / monodromy (feasibility 1/10, now a no-go)
Vacuous at fixed q (conductor `f^r≈p^{3/4}` explodes; discrepancy `m/√q=2^48`). Depth-sparsity **refuted** this
session (depth D grows ~2r). The **modern post-2015 toolkit is now a theorem-level NO-GO** (ℓ²-decoupling/BDG,
efficient congruencing/VMVT, F_p restriction, coset-doubling): all 0/5 beat n^0.989 because they extract power
from **curvature** and μ_n is **flat** (0-dim, d=1 where Stein–Tomas is singular; η_b is degree-1 in x so VMVT's
degree-≥2 savings are inapplicable). Dead.

### #5 — Saddle / large-deviation (feasibility = #1; it's the *consumer*, not a separate avenue)
The cosh-MGF saddle reaches the floor (`M ≤ √(2e·n·(ln q+1))`, `_AR_MomentOptimizedSupNorm`) **given** the W1
envelope. So #5 is the *output stage* of #1, not independent. Its missing input is W1's envelope = avenue #1.

### #6 — Growth-law generating function (feasibility 3/10, off-BGK but reduces under antipodal)
The coset-union ζ `Z(t)=exp(Σ_r I_r t^r/r)` rationality / pole structure for `m*`. Genuinely off-BGK in form,
but the object **= the μ_{n/2} thin-Sidon/BCHKS-1.12 wall under the antipodal identification** (§6.5). The n=64
exact measurement is compute-heavy (the prior workflow stalled on it). Independent in spirit, reduces in content.

---

## 2. The single most promising path + its exact missing input

**Path: #1, specifically the W3-antitone OR F2-contractivity per-level sign condition, with the W1 MGF envelope
as the target form.**

Why this pair: both reduce the all-depth bound to a **finite base** (proven, r=1: `M_4≤3n·M_2`) **+ a single
per-level sign condition** — the cleanest possible surface. F2 additionally carries a **proven strictly-negative
principal-subtraction term** `−(2^{2r}−2)|H|^{2r}` that the dead magnitude-tower never had; this is genuine
contractivity, not the geomean-tower that failed in §8.

**Exact missing proven input (one statement, three equivalent dresses):**
> A **char-p hypercontractive / log-Sobolev estimate** for the cyclotomic moment recursion of μ_n at depth
> r~log q, sufficient to give *either* `StepRatioAntitone` (R(r)=E_{r+1}/((2r+1)·n·E_r) is ≤1 / antitone)
> *or* the per-dyadic-level `RhoContractiveAtDepth` (`Cum(μ_n,r*)≤2·Cum(μ_{n/2},r*)`) — equivalently, a bound on
> the spurious cyclotomic-norm-divisibility count `Spur_r(p) ≤ n^{2r}/p` at the prize prime (W7).

This input is **open** but is the most plausible because: (a) char-0 is fully proven, (b) the MGF envelope it
must produce already holds numerically to n=256, (c) it only needs to hold in **aggregate** (per-coefficient
failures are absorbed — the W1 insight), and (d) the negative principal-subtraction term gives real slack.

**Concrete first step:** attack `StepRatioAntitone` (W3) / `RhoContractiveAtDepth` (F2) analytically — try to
derive the per-level sign condition from a char-p Bonami–Beckner/log-Sobolev inequality on the dyadic tower,
using the proven negative correction term. In parallel, *confirm the target* by extending the W1 MGF-envelope
numerics to n=512/1024 across several structured primes (cheap; if the envelope ratio stays ≤1 robustly, the
right target is locked).

---

## 3. Is there a proven literature theorem the campaign missed?

**Skeptical answer: no.** Every "proven input" route hits the good-prime/bad-prime threshold (the char-p lift is
super-polynomial in the prize prime). The honest *untried* framings (not foreclosed, but each prize-hard) worth
a genuine attempt:
- **Subconvexity ⟹ effective-QUE** (comments 21/23): η_b = Gauss sum τ(χ) over the n characters trivial on μ_n;
  reframe M(n) as an effective equidistribution rate of the μ_n-orbit and seek the analogue of "QUE rate from a
  subconvex L-function bound" (Watson triple-product) in the conductor aspect. **Untried in-tree.** Replaces the
  2nd-moment program with a single subconvex bound — but subconvexity at the relevant family is itself open.
- **Equitable-partition quotient interlacing** (comment 22): the m=2^128 μ_n-cosets give an exact m×m quotient
  whose eigenvalues interlace λ₂ with **no Markov loss** — turns the sup-norm into a coset-collision-matrix
  question. Untried for μ_n.
- **η'_b critical-point / Palm conditioning** (comment 73): the law of η_b given η'_b=0 has strictly smaller
  *tail* — the genuine first-b-derivative lever the symmetric-moment meta-theorem (§4) provably cannot reproduce.

---

## 4. Honest meta-verdict — the bottleneck is ONE type of input

All six avenues, stripped down, share a single bottleneck: **char-p (mod-p) control of the deep cyclotomic
moment at depth r~log q for the *specific* prize prime** — the spurious-norm-divisibility count `Spur_r(p)`,
equivalently a hypercontractive/counting-transference statement. Avenue #1 has reduced this to its sharpest,
most-favorable form (aggregate MGF envelope, char-0 proven, numerics holding to n=256, a proven negative slack
term). Avenues #2–4 are the same wall in analytic/geometric/sheaf clothing and offer no proven input that beats
the prize prime. The required input is **a new char-p concentration/hypercontractivity result at the Burgess
barrier** — exactly the type the campaign has consistently identified as the genuinely-new mathematics needed.

**Best next action.** Attack the W3 `StepRatioAntitone` / F2 `RhoContractiveAtDepth` per-level sign condition
(finite base proven; negative correction proven; only the sign at depth open) as the single cleanest provable
surface, and lock the target by extending the W1 MGF-envelope numerics. This is the one place where a *finite +
sign* statement — not a full half-power character-sum miracle — could close the prize.
