# Proving δ\* in the Prize Regime — A Research Paper (#444)

*A complete, honest account of the open directions for pinning the mutual-correlated-agreement
threshold of explicit dyadic Reed–Solomon codes, with 25 research directions and 25 proposed
new mathematics, each defended for novelty, closedness, and tractability — then shredded.*

> **Honesty contract.** This paper labels every claim by status. "Open" means a recognized open
> problem. "Closed" means the proof reduces only to already-proven mathematics or a finite
> computation. A direction that secretly reduces to the BGK/Paley wall, to the Johnson bound, or
> to another open conjecture is **larp** and is marked as such in the critical pass (§4–§5).

## §0. The exact target and the exact wall

**Target.** Pin `δ* = sup{ δ : I(δ) ≤ q·ε* }`, the worst-case far-line incidence threshold, in the
**prize regime**: dyadic FFT subgroup `μ_n ⊊ F_q*`, `n = 2^μ ~ 2^30`, `q = n^β` prime with
`β ≈ 4–5`, `ε* = 2^-128`, budget `q·ε* ≈ n`, fixed index `m = (q-1)/n = 2^128`, **thin**
`n = q^{1/β} ≪ √q`. Rate `ρ = k/n`. Window interior `(1−√ρ, 1−ρ−Θ(1/log n))` — strictly between
Johnson (achievable) and capacity (proven impossible). The governing identity
`δ* = sup{δ : I(δ) ≤ q·ε*}` is in-tree and exact; extremal lines are **monomial directions**
`(X^a, X^b)` by the `Z/n` dilation symmetry.

**The wall.** Essentially every analytic attack reduces to bounding the **thin dyadic Gauss-period
sup-norm**

> `B = max_{b≠0} |η_b|`, where `η_b = Σ_{x∈μ_n} e_q(b x)` — the non-principal eigenvalue of the
> generalized Paley graph `Cay(F_q, μ_n)`.

The prize needs `B ≤ √(n · polylog)` (square-root cancellation up to log). The best **proven** bound
is BGK `n^{1-1/2880}`, which requires `n > q^{1/4}` — **violated** by the thin prize point. This is
the **Burgess barrier**: for subgroups below `√q`, no unconditional sub-`√q` character-sum bound is
known, and the campaign has machine-verified that ~25 distinct "faces" (BCHKS-1.12 `s=1` crossCell,
the char-`p` deep moment, the cumulant dyadic descent, the spectral `λ₂`/Parseval floor, the
cosh-MGF/Bessel saddle, the Kelley–Owen dilation pencil, the Schur-minor staircase, Lam–Leung
antipodal classification, the line-decoding/collinearity object, the DFT-uncertainty/Chebotarev
reframing, …) all collapse to exactly this `B`. **Refuted outright** (not merely walled): capacity,
the additive-energy route (√-lossy: `E=t² ⟹ list n^{3/2}`, sub-Johnson), Stepanov/Weil (vacuous for
`n < √q`), Burgess/Heath-Brown–Konyagin (`q^{1/3}`-blind), Khovanskii fewnomial, the structure-aware
norm gate past `n=32`, the 2-adic reverse-descent leg, the moment method past `r ≈ β+1`.

This is not pessimism; it is the **map**. A winning direction must do one of three things, each of
which is a recognized survivor after a 22-agent triage of 179 avenues:

## §1. The three genuine survivors (why each is still open and available)

### A1 — Exploit smoothness: the Weil normalizer-pencil energy gap (NOT a character sum)

**The lever.** Every wall reduction treats `μ_n` *abstractly* — as an arbitrary multiplicative
subgroup — and is therefore **blind to the explicit smoothness** `x_i = g^i` that defines the prize
code. The single structural fact distinguishing the prize code from a generic thin subgroup is that
the evaluation points form a **geometric progression**. The third (factorial) moment `M3` of the
explicit smooth-`μ_n` agreement list *exceeds* the random-RS value by **exactly** the
torus-normalizer involution energy `~ n⁴/8` — and crucially this excess is a **conic/curve incidence
count** (a Weil (1,1)-pencil), **not** a character sum. It is therefore *a priori* outside the wall:
no `B = max|η_b|` bound governs it.

**Why open.** The signal has never been pushed to a δ\*-pinning inequality. The verified
non-normalizer Weil bound `t₂ = O(n²/q + 1)` gives only a `q^{-4}` `M3` signal — possibly too small.

**Why closed (if it works).** A conic-incidence count over `F_q` is governed by Weil II /
Deligne — *proven* mathematics. The object to pin is a **closed cyclotomic identity** for `P3(t₂)`
(subgroup vs. random) at fixed `n`, then a **fractional-cover / LP certificate** on the explicit
`35 × 1344` normalizer-incidence matrix. Both are finite/decidable. No open residual *if* the signal
is large enough.

**Next concrete step.** Derive the closed cyclotomic `P3(t₂)`; feed the normalizer-incidence matrix
to a fractional-cover LP; push to `M4, M5` for a larger normalizer signal.

### A2 — The cardinality lane: count `#distinct-γ` at the Johnson radius (off the meta-theorem)

**The lever.** The MCA bad-scalar object is a list-decoding **cardinality** — an exponential-growth-
class object — which the campaign *proved* is **distinct** from the second-order-moment quantity the
"no third route" meta-theorem rules out (`E2-count ≠ char-sum`, disproven). Therefore the cardinality
is **not** capped by the meta-theorem. The live prize sits at the **Johnson-scale radius**
`a ≈ √(kn)`, where the list size *could* be polynomial in `n` rather than character-sum-controlled.

**Why open.** Prior census Props bounded the wrong object (`#alignable-SETS`, dead at 2–4× budget);
the correct object `#distinct-γ` measures `~0.20·budget` at `n=32` with margin not tightening — i.e.
genuinely sub-budget but unproven.

**Why closed (if it works).** A cardinality bound via the container method, a transfer-matrix /
generating-function count of monomial-line incidences, or a Frankl–Wilson / Fisher-type design bound
is *combinatorial* and finite-checkable. The risk is that any tight enough count silently re-imports
`B`.

**Next concrete step.** Land a `BadScalarCensus` Prop over `#distinct-γ`, re-weld δ\* to it, and bound
`#distinct-γ` at `a ≈ √(kn)` by a container/transfer-matrix argument.

### A3 — The abandoned half: push δ\* UP past half-Johnson (a lower bound, not a ceiling)

**The lever.** The entire campaign bounded δ\* only from *above* (ceilings). The *floor* was never
pushed past `(1−√ρ)/2`. A constructive lower bound — an explicit bad family forcing δ\* high — is the
one direction the forward Johnson machinery **structurally cannot** produce, and it sidesteps every
sup-norm wall because it *constructs* rather than *bounds*.

**Why open.** Fold-based lower bounds need `cl(E) ≥ 1−√ρ`; the squaring tower's antipodal blocks
provably don't align (co-location `~0.40`), so only an *adaptive* fold works — leaving the GG25 frame.

**Why closed (if it works).** An explicit construction + an exact incidence count is finite. The
reverse LD⇒MCA dictionary (`exists_interleavedList_card_gt_of_epsMCA_gt`) converts a list-size lower
bound into an MCA lower bound with no open residual.

**Next concrete step.** Run the reverse LD⇒MCA dictionary at `n > 16`; search for an explicit
adaptive-fold bad family on `μ_n` with super-polynomial list at `a ≈ √(kn)`.

## §2–§3. Twenty-five research directions + twenty-five new mathematics

*(generated and adversarially shredded by the `prize-paper-generate-and-shred` engine; the surviving,
ranked subset and the no-larp abstract are appended below as they complete — see §4.)*

## §4. The critical pass (no larp)

*(the shred verdicts: which directions reduce to the wall, to Johnson, to open math, or are larp;
and the precise condition under which each survivor would close. Appended on engine completion.)*
