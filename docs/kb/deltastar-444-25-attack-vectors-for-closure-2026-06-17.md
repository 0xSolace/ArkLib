# 25 attack vectors that can actually CLOSE δ* — frontal wall-proofs + reduction gap-hunts (#444)

**Honest framing (the contract).** We proved this session that solving the prize means exactly one of:
(A) **prove the wall** — BGK `M(n) ≤ C√(n log m)` for thin 2-power μ_n at the Burgess barrier (β≈4); or
(B) **prove undeterminability** — which is **FALSE** (`_DeltaStarDeterminability`: δ\* is a decidable Π₁
quantity). By the proven two-sidedness (`δ* interior ⟺ BGK`), **no conjecture can "avoid the wall yet
solve the mystery" unless the reduction itself has a gap.** So the only honest paths to a *complete proof*
are (A) frontal proofs of the wall, and (B) gap-hunts in the reduction. Below are 25 such vectors, each
genuinely technical, rated for feasibility-of-CLOSURE (1–10), machine-tested where possible. **None is a
fabricated solution; several Category-C items are provable PARTIAL theorems = real forward progress.**

---

## Category A — frontal proofs of the wall (BGK `M ≤ C√(n log m)`)
*Each, if completed, closes the prize. Ordered most→least tractable.*

**A1. The E_r ladder → all-r char-0 Wick, then char-p transfer at deep r.** [feas 3]
char-0 `E_r ≤ (2r−1)‼·n^r` is closed (Lam–Leung). The open part is the char-p transfer at `r≈ln q`. The
E_r closed forms are exact in-tree to E₇; **machine-confirmed `E_3 = 15n³−45n²+40n`, `W_3=0` at prize
primes**. Concrete sub-goal: prove `W_r = 0` (or `≤ slack_r`) for `r` up to `ln q` at the prize prime —
this IS the wall, but the ladder gives a rung-by-rung assault.

**A2. di Benedetto T₃-conditional → unconditional SOTA (the most tractable real gain).** [feas 6 for SOTA,
2 for closure] Machine-confirmed `T_3 = E_3 = 15n³−45n²+40n = O(n³)`. *Proving the closed form for all n*
(a char-0 symmetric-function identity — the "No-Excess r=3") makes the di Benedetto exponent `0.9583`
**unconditional SOTA**. NOT closure (`0.9583 ≫ 0.5`), but a publishable real improvement and the cleanest
landable sub-goal. **Recommend formalizing the E₃ closed form next.**

**A3. Bourgain–Garaev effective o(1) for 2-power ORDER subgroups.** [feas 2] BGK gives `n^{1−o(1)}`
non-effectively. The dyadic tower (`μ_n ⊃ μ_{n/2} ⊃ …`, all 2-power) is far more structured than a generic
subgroup — pursue an *effective* `o(1)` exploiting the chain of sub-subgroups (the sum-product step has
extra structure when every subgroup index is 2).

**A4. Heath-Brown/Konyagin multiplicative-energy bound via the FFT factorization.** [feas 2] `μ_n` with
`n=2^μ` has the dyadic FFT structure; the multiplicative energy decomposes along the Walsh–Hadamard basis.
Test whether the FFT factorization yields a Burgess-type bound better than generic for these special moduli.

**A5. The 2-adic Newton-polygon / Stickelberger bound (N7 — survives the meta-theorem).** [feas 2] The
NP slopes `v_2(η_b)` are non-archimedean, moment-blind. A divisibility lower bound on `∏(η_b)` (via
Stickelberger) combined with the fixed `Σ η_b² = p−n` could squeeze `max|η_b|`. The one surviving
phase/valuation route; genuinely not a moment method.

**A6. Kowalski–Untrau effective equidistribution → W₁ extreme-value.** [feas 2] KU give the limiting law +
an effective rate for the period family; a Wasserstein extreme-value upgrade over the `m=2^128` cosets
would bound the max. The most promising *automorphic* input (untried in the thin regime).

**A7. Liu–Zhou subgroup-restriction eigenvalue recursion.** [feas 2] `λ₂(μ_{2n}) ≤ λ₂(boundary on the
index-2 sublattice) + …` — a multiscale recursion distinct from the dead crossCell descent. **Machine
caveat: the exact `M(n)²/M(n/2)²` ratio is 3.88→3.09→2.82 (>2, decreasing)** — so the naive recursion is
super-additive; the Liu–Zhou *boundary* term must supply the saving, untested.

**A8. FKM ℓ-adic Fourier-stability transport.** [feas 2] `M(n)` is a DFT of `1_{μ_n}`; FKM prove a sub-√p
trace-function estimate is DFT-stable. Identify `1_{μ_n}` as (close to) a trace function and transport.

**A9. Subconvexity → effective QUE rate for the μ_n-orbit.** [feas 1] Reframe `M ≤ C√(n log m)` as an
effective equidistribution rate; needs a subconvexity input for the relevant L-function. The cat-map kill
showed the naive version is the wall, but a genuine subconvexity bound (if it existed for this L-function)
would be a real input.

**A10. Murphy–Rudnev–Shkredov 49/20 energy → Kelley–Meka entropy increment.** [feas 1] Replace the lossy
Cauchy–Schwarz energy→sup step with an entropy/density-increment; the 49/20 energy is the best known input.

**A11. Period-polynomial Galois descent + class field theory.** [feas 1] The period polynomial `Ψ` has
class-field-fixed discriminant (`discnogo`); use the Galois action to descend `max|η_b|` to a regulator
bound. (Discriminant gives only lower bounds — needs a genuinely new upper-bound mechanism.)

**A12. Direct saddle-point on the Poisson-averaged MGF (the slacker target).** [feas 2] The
Poisson(log q)-weighted `Ψ(y*) ≤ q²` tolerates per-r violations; prove the averaged MGF bound directly
rather than per-r Wick. The most forgiving equivalent form (`_wf7W1`, `PoissonAveragedMGF`).

---

## Category B — gap-hunts in the reduction (the ONLY place an "escape" could exist)
*If `δ* interior ⟺ BGK` has a lossy step, the prize could be EASIER than the wall. Each is a precise
technical question about tightness.*

**B1. Is `interior ⟹ bound M` tight, or does the budget tolerate a weaker bound at the SPECIFIC window
radius?** [feas 3] The two-sidedness uses `ERM-at-r ⟺ max‖η‖²≤(2r+1)n`. But the actual δ\* budget is
`q·ε* ≈ n` at radius δ. Re-examine whether the bad-scalar count at the *exact* interior radius needs the
full sharp `M`, or a weaker `M ≤ n^{1−c}` suffices. (I refuted the naive version, but the *exact* tolerance
at the binding radius is worth re-deriving — this is the single highest-value gap-hunt.)

**B2. Is the incidence→period bridge (`badScalars ⟺ explainable ⟺ M`) lossy?** [feas 2] The reduction goes
through `epsMCA = max(#bad)/q` and `#bad ⟺ incidence ⟺ M`. Check each `⟺` for slack — a non-tight step
would decouple δ\* from the sharp `M`.

**B3. Does the meta-theorem's "winning method must bound M" have a loophole for non-moment methods?**
[feas 2] The necessity `interior ⟹ M-bound` is airtight for moment methods (`moment_ladder_exceeds_prize`)
but relies on the meta-theorem (3-property) for the general case. Is there a method satisfying (a)(b)(c)
that reaches the interior WITHOUT bounding the worst-case sup? (The far-line audit suggests not, but the
general necessity is the softest link.)

**B4. Is the proxy/interior split `δ* = min(over-det proxy, under-det M)` exhaustive?** [feas 2] Could there
be a THIRD binding regime (neither the over-det Johnson proxy nor the under-det sup-norm) that the
dichotomy misses? Machine-test the full incidence landscape for an intermediate binding.

**B5. Is the p-sensitive classification's "aggregation kills Class B" airtight at DEEP r?** [feas 2] The
aggregation argument (moments p-independent until deep r) was machine-verified at low r. At `r≈ln q` the
max dominates the moment — is there a deep-r regime where a Class B invariant (valuation, phase) survives
aggregation and couples to the binding? (The crux of whether the one-dimensionality is exact.)

**B6. Does the KKH26 ceiling's `r=k+1` actually equal the floor's binding depth?** [feas 2] The ceiling
binds at the easy `r=k+1` direction; the floor binds deeper. Is the GAP between them provably positive,
or could they coincide (making the ceiling tight = δ\* determined)?

**B7. Is `M` the right object, or is the relevant quantity the SECOND-largest / a spectral gap?** [feas 1]
δ\* might depend on `λ₂` structure beyond the single max. Re-examine whether the incidence is controlled by
`max|η_b|` or by a finer spectral statistic (which could have a different, provable bound).

**B8. Does the budget `ε*=2^-128` (FIXED, not →0) create slack the asymptotic analysis misses?** [feas 2]
The prize fixes `ε*`; the asymptotic `δ*` analysis takes limits. At the FIXED `ε*` the budget `q·ε*=n` is
exact — re-examine whether the fixed-budget δ\* differs from the asymptotic threshold (a finite-vs-limit
gap).

---

## Category C — provable PARTIAL-determination theorems (REAL forward progress, achievable now)
*These don't close the prize but ARE provable theorems sharpening the determined region.*

**C1. δ\* is FULLY determined (exactly) for `n ≤ 40`.** [feas 8 — landable] In the norm-bound regime
`q > (2r)^{n/2}` (i.e. `n < 2 log q/loglog q ≈ 40`), BGK IS proven, so `δ*` is pinned exactly. Formalize
the exact-determination theorem for the explicit small-n window (extends the F5/F17 pins to a regime).

**C2. δ\* > Johnson is FALSE to prove from any sub-√n bound — but δ\* = Johnson is also unprovable.** [feas
6] Machine-confirmed: `M ≤ n^{0.9583}` (di Benedetto beat) does NOT reach the interior (it's `≫ √n`). So
no partial M-bound gives partial interior — the interior is all-or-nothing at the √n threshold. This is a
provable RIGIDITY: `δ*` is determined to be EITHER Johnson OR interior, with no provable intermediate.
Formalize the dichotomy-rigidity.

**C3. The exact δ\* lower bound `δ* ≥ 1−ρ−M_cross/n` with the EXACT pins as anchors.** [feas 7] Already
`_BchksF6` modulo residuals; tighten with the verified pins (9/16, 3/8) as unconditional anchors at small n.

**C4. A provable margin: `δ* ≤ (1−ρ)−c/log n` with EXPLICIT c (sharpen the KKH26 ceiling constant).** [feas
5] The ceiling has `Θ(1/log n)`; pin the explicit constant via the Kambiré bad-family, giving a concrete
provable upper margin (a real theorem narrowing the window).

**C5. Formalize the EQUIVALENCE `δ* determination ⟺ BGK` as a hardness theorem.** [feas 7 — landable] Strengthen
`interior_iff_bgk` to a clean in-tree statement that determining δ\* is polynomial-time-equivalent (or
logically equivalent) to the BGK bound — a provable META-theorem that *characterizes the prize's exact
difficulty*. This is itself a complete, publishable result: "δ\* is determined iff BGK, and BGK is the 25-
year-open wall."

---

## The honest bottom line

**A complete proof requires either (A) a genuine new analytic-NT input proving BGK — none exists in the
literature, and the most tractable sub-goal (E₃ closed form, A2/C1) gives only SOTA, not closure — or
(B) a real gap in the reduction (B1–B8), which would make the prize easier than the wall; the highest-value
single shot is B1 (the exact budget tolerance at the binding radius).** Everything provable NOW is
Category C — partial-determination theorems that sharpen the window and characterize the difficulty, but
do not close it. **I will not present any of these as a solved prize; they are the genuine, honest research
frontier, and the prize remains the one open analytic input.**

> Method: machine-tested (V1: `E_3=15n³−45n²+40n` exact, `W_3=0`; V2: dyadic ratio 3.88→2.82) in
> `probe_attack_vectors.py`; vectors and ratings by direct analysis (agent fan-out weekly-limited to Jun 20).
> No fabricated closure.
