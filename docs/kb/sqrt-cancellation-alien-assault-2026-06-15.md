# Effective √-Cancellation Assault — Twelve Alien Mechanisms, Honest Synthesis

**Target (#444).** `M(n) = max_{b≢0 (p)} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m)`, `C = O(1)`,
`n = 2^μ`, `p ≈ n^4` (β=4, Burgess barrier), `m = (p−1)/n ≈ 2^128`. This is the BGK/Paley
thin-subgroup √-cancellation wall — ~25 years open, equivalently char-p validity of the
DC-subtracted moment `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r ≈ ln q ≈ 89`
(= BCHKS-1.12, s=1).

**Necessary condition (dossier §4, c.4705921074), the screen every mechanism must pass:**
any winning method is simultaneously **(a) b-sensitive**, **(b) deterministic-archimedean**
(NOT probabilistic-EVT), **(c) genuinely L∞** (sup, not RMS/L²). The meta-theorem
`(q·E_r)^{1/2r} ≥ n` kills *every* second-order/moment/energy/spectral/SDP method as a theorem.

**Independent confirmation run this session** (`/tmp/prizepaper/confirm_probe.py`, exact,
coset-reduced, β=4, n=8..128):

| n | p | m | p/m | M | √(2n ln m) | M/tgt | tail@5σ / Gaussian |
|---|---|---|----|---|-----------|-------|--------------------|
| 8 | 4073 | 509 | 8.00 | 7.537 | 9.986 | 0.755 | 2.92× |
| 16 | 65537 | 4096 | 16.00 | 13.838 | 16.315 | 0.848 | 3.77× |
| 32 | 1048609 | 32769 | 32.00 | 22.983 | 25.796 | 0.891 | 3.54× |
| 64 | 16777153 | 262143 | 64.00 | 37.436 | 39.963 | 0.937 | 3.66× |
| 128 | 268437889 | 2097171 | 128.00 | 51.389 | 61.044 | 0.842 | 3.70× |

Three facts this pins, used throughout below: **p/m = n EXACTLY** (so the target √(2n ln m) is
*identically* the free-phase extreme-value value √(2·(p/m)·ln m)); **M/target ∈ [0.76, 0.94]**
(target is real and near-tight); and the **5σ tail is 2.9–3.8× heavier than Gaussian and stable
in n** — the "two-value normalizer spike." This last number is the executioner of the whole
EVT/SUSY/positivity class.

---

## 1. RANKED VERDICT

**Survivors that genuinely yield √(n log m), are non-moment, pass (a)+(b)+(c), AND do not reduce
to the wall: ZERO.** All twelve fail. None cracked it; none even partially escaped. But they did
not fail uniformly — they cleave into a strict taxonomy, and the *manner* of failure is the
payload of this report.

The honest ranking is by **how rigorous the kill is** (least-dead = highest), because a
non-rigorous kill is where a future attack could still live.

| Rank | Mechanism | Passes (a)(b)(c)? | Fails by | Kill rigor |
|------|-----------|-------------------|----------|------------|
| 1 | **Information-theory: deterministic discrepancy (Koksma-Hlawka)** | **ALL THREE** | **circular-to-M** (thin-orbit D* = M/n) | numeric O(1), but the non-circular *form* survives |
| 2 | **Geometry of numbers: Banaszczyk transference/smoothing** | (c) only | reduces-to-moment (only √n = energy; lattice b-blind) | numeric, sharp |
| 3 | **Algebra: hidden Gauss-sum variety / Jacobi cocycle** | ALL THREE | **circular** (cocycle full-rank; J built from same g) | prime-independent theorem (full rank) |
| 4 | Analysis: Bourgain bootstrap / Salem-Zygmund | ALL THREE (by restating target) | circular-to-M (flat full-support coeffs) | numeric (zero lacunarity) |
| 5 | Physics/opt: conformal-bootstrap positivity / SOS | (a)(c) | **Weil √q** (phase-blind ⇒ aligned adversary = √p) | numeric, adversary explicit |
| 6 | Number theory: Mahler-measure / Galois-house | (b) only | reduces-to-moment + circular (orbit = period family) | structural (q prime ⇒ f=1) |
| 7 | Operator space: non-normal dilations / Toeplitz / Crouzeix | (a)(c) | **dichotomy**: =M (circular) or <M (useless) or Θ(n) phase-blind | exact dichotomy, verified |
| 8 | Physics: fermionic/Grassmann + SUSY localization | (b) only | reduces-to-moment/EVT (SUSY saddle = Gaussian tail; rank-1 trap) | numeric (heavier tail) |
| 9 | Quantum: unitary scattering / S-matrix | none | **L² conservation** (Parseval RMS=√n; log m is EVT) | numeric, sharp |
| 10 | Harmonic: dyadic-cube decoupling (Bourgain-Demeter/BL) | (c) | reduces-to-moment (zero curvature, rank-1 BL); FALSE depth-μ bound | 24/24 falsification |
| 11 | Algebra: total positivity / Gantmacher-Krein | (b) only | **phase-blind ⇒ trivial n** (dies BEFORE the wall) | numeric (31–44% neg minors) |
| 12 | Wildcard: dynamical/transfer-operator (+4 others) | varies | **cocycle closure L_b^n = I ⇒ circular** | theorem-grade identity |

---

## 2. HOW EACH FAILS — the precise failure mode

The twelve deaths reduce to exactly **four** mechanisms, plus one mechanism that dies *before*
even reaching them. This is itself a structural finding: there are only four ways to be wrong.

**(I) REDUCES-TO-MOMENT / EVT** — the √n is the L² energy `Σ|η_b|² = pn − n²` and the √(log)
is probabilistic extreme-value over m exchangeable channels.
- **Banaszczyk transference (#2):** the only √n it produces is `rms = √(energy/(p−1))` = the dead
  L² moment; the cyclotomic lattice `Z[ζ_p]` is well-rounded (all minima ~√p, smoothing param
  ~1/√p → 0), so it carries **no √n invariant at all**, and applying Banaszczyk to a *specific*
  dense point η_b requires asserting it is balanced at the √n shell = the house bound itself.
- **SUSY/fermionic (#8):** fermion-boson determinant cancellation localizes onto a Gaussian
  saddle = iid/exchangeable EVT value √(2n log m); but the rank-1 trap (η_b is a single inner
  product 1*w, one fermionic mode — det(I+ww*) = 1+n is b-BLIND, Pfaffian of the rank-2 phase
  matrix ≡ 0) means the only b-sensitive determinant is the circulant whose op-norm IS M. The
  probe's heavier-than-Gaussian tail (2.9–3.8×) proves the SUSY value is **not** a rigorous
  upper bound — the corrections are the high cumulants = the dead moment route.
- **Dyadic-cube decoupling (#10):** the digit-product lift `ζ^j = ∏ g_i^{c_i}` is a *bijective
  re-coordinatization of the same flat lacunary line* — zero second fundamental form (exponent
  affine in digits), rank-1 Brascamp-Lieb datum (g_i collinear powers of one ζ). The bound a
  genuine BD/BL decoupling would give, `M ≤ √(2n log₂ n)`, is **FALSE 24/24** (violation grows
  with β) because the intrinsic scale is log m = β log₂ n, not the cube depth.
- **Mahler/Galois-house (#6):** the m Galois conjugates of η_b ARE the m periods, so any
  symmetric functional (norm, trace, elem. symmetric, Mahler) = power sums = moments; rms over
  the orbit = √n exactly (Parseval), spread = house/rms = the √(log m) wall verbatim. Plus a
  premise larp: η_b lives in K ⊂ Q(ζ_p) of conductor = odd prime p, NOT Q(ζ_{2^μ}), so all
  "2-power cyclotomic Mahler" theory is inapplicable (q prime ⇒ residue degree f=1).

**(II) CIRCULAR-TO-M** — the object literally equals the operator norm of the period circulant,
whose eigenvalues are the η_b.
- **Bourgain bootstrap / Salem-Zygmund (#4):** recasting M as the sup-norm of the
  flat-coefficient cyclic Gauss-polynomial f(j) = η_{g^j} is exact but the cyclic DFT has
  sup-norm = M *by construction*; Salem-Zygmund's √(log) is a theorem only for **lacunary/Sidon**
  frequency sets, and the Gauss coefficients are **flat with full support (zero lacunarity)**, so
  asserting SZ here IS the BGK conjecture. No self-improving operator Φ exists numerically
  (M/√(n ln m) plateaus AT the target ~1.2–1.4, no contraction).
- **Gauss-sum variety / Jacobi cocycle (#3):** the cocycle relation matrix on Z/m is
  **full-rank for every m** (prime-independent), so dim(variety) = m−1, not O(log m); and
  J(χ1,χ2) = g(χ1)g(χ2)/g(χ1χ2) is built from the same g's, so "θ pinned by arg J" is a
  tautology with zero independent content. The phases are spectrally flat white noise.
- **Dynamical/transfer-operator (#12):** the cocycle-closure identity **L_b^n = I** (forced by
  h^n = 1: `∏_{j} e_p(b h^{−j} x) = e_p(b x · Σ h^{−j}) = e_p(0) = 1`) pins the weighted transfer
  operator to a unitary of order exactly n, reconstructing the n-circulant whose op-norm is M.
  This is a *new* theorem-grade reason the entire dynamical-zeta / thermodynamic-formalism class
  is circular (not previously in §8's EVT/RMT/ergodic list).
- **Discrepancy (#1):** for a thin orbit of size n = p^{1/4}, the star-discrepancy
  `D*_b = Θ(|η_b|/n)` — Koksma-Hlawka just restates `|η_b| = Θ(n·D*_b)`; Erdős-Turán bounds D*
  by the exp sums (wrong direction); the only a-priori LCG discrepancy bound (Korobov-Niederreiter
  O(log p / N)) **requires the full period ~p**, not a size-n=p^{1/4} orbit. (See §3 — this one's
  *form* is not dead.)

**(III) WEIL √q / PHASE-BLIND** — accesses only moduli (|g(χ)| = √q) and phase-DIFFERENCES, never
absolute phases; the phase-aligned adversary (consistent with all such invariants) achieves √p.
- **Conformal-bootstrap positivity / SOS (#5):** the period DFT has perfectly flat modulus √p on
  all m−1 nonzero freqs; an SOS certificate sees only |ĥE_k|² = p and HD/Jacobi phase-differences,
  so the bootstrap **ceiling is √p ~ n²** (a factor √(m/log m) above target, GROWING). The exact
  identity p/m = n forces the target to *be* the free-phase EVT value — and EVT is dead.

**(IV) L² CONSERVATION — pins RMS, not sup**
- **Unitary scattering (#9):** unitarity/Parseval fixes `Σ_b |η_b|² = nq` ⇒ RMS = √n; the only
  bound is the trivial Cauchy-Schwarz √(nq); the log m is supplied **entirely** by EVT over m
  exchangeable channels (max/RMS = √(2 ln #chan), matched to 2 digits). The doubling-map step is
  non-invertible (2-to-1) so it cannot even *be* a unitary walk.

**(V) DIES BEFORE THE WALL — trivial-n, phase-blind by construction**
- **Total positivity / Gantmacher-Krein (#11):** no TP representation exists (every real form —
  Re, Im, value-sorted, even the PSD Gram CC* — has 31–44% negative 2×2 minors; variation-
  diminishing violated), and *even granting* TP, Perron bounds the top eigenvalue by the row-sum,
  which for an all-unit-modulus operator is **identically n** = the trivial L¹/triangle bound. TP
  controls positive combinations and is structurally blind to phase cancellation. The same
  oscillation that produces √-cancellation destroys total positivity — they are the same
  phenomenon. (Genuinely alien — zero prior mentions — but dies at trivial n, before BGK.)
- **Operator-space dilations (#7):** strict dichotomy — any norm ≥ M that dominates the spectrum
  is pinned AT M (the full Toeplitz section with wraparound IS the circulant); every non-normal
  truncation (lower-triangular L, numerical radius, Stinespring) drops the wraparound mass and
  lands strictly BELOW M (0.55–0.70·M), useless as an upper bound; the only spectrum-free
  certificate (Schur/Frobenius/Crouzeix) is phase-blind and gives Θ(n) (Crouzeix even Θ(n²)).

---

## 3. SURVIVING / LEAST-DEAD MECHANISMS — ranked by promise, with sharpest next probe

No mechanism survives as a *bound*. But three have a kill that is **numeric, not a theorem** — the
honest frontier is exactly the gap between "verified circular/dead at n≤128" and "proven dead."

### LEAD 1 (most promising) — Deterministic individual discrepancy (Koksma-Hlawka), #1.

**Why it is the least-dead.** It is the *only* mechanism that passes all three necessary-condition
properties **without restating the target and without invoking moments or probability.** The
reduction is exact and reusable:

> `|η_b| ≤ V·n·D*_b` (V = O(1), Koksma-Hlawka), so
> **`M(n) ≤ C√(n log m)` ⟺ `D*_b ≤ C√(log m / n)` for every b.**

This is a genuine *reframing* of the prize as a **uniform individual star-discrepancy bound on the
thin orbit** — b-sensitive (D*_b depends on b; the worst-D* coset = worst-M coset, corr 0.844),
deterministic-archimedean (discrepancy on [0,1), no ensemble), genuinely L∞ (sup over intervals).
The kill is circularity *for thin orbits* (D* = Θ(M/n)), verified only numerically to O(1).

**Sharpest next probe/derivation.** The circularity is `D*_b = Θ(|η_b|/n)` — but that estimate uses
*only the n points of the orbit*. The non-circular content would be a discrepancy bound that uses
the **arithmetic of the LCG multiplier h = g^{(p−1)/n}** (continued-fraction / Dedekind-sum
structure of the orbit step), not the orbit cardinality. The probe to run: compute the **continued
fraction expansion of h/p** (and of bh/p for the worst b), and test whether the worst-coset
discrepancy correlates with the **partial-quotient sum / Ostrowski digits** rather than with M
itself. Concretely:
- For n = 8..128, worst b: does `n·D*_b` track `Σ a_i` (sum of partial quotients of bh/p) or track
  M? If it tracks `Σ a_i` *independently of M*, there is a non-circular handle (this is the
  three-distance / Steinhaus structure of a single rotation lifted to the orbit).
- **Expected outcome (honest prediction):** it tracks M, because the size-n orbit is too short to
  see the full continued-fraction period — confirming the dossier's "Korobov needs the full
  period." But if the partial-quotient sum is *bounded* for the structured 2-power multiplier h
  (a Diophantine property of h = g^{(p−1)/2^μ}), that is a genuine off-wall lever. This is the one
  derivation in the entire assault that is *not* obviously circular before running.

### LEAD 2 — Banaszczyk √(2 log N) inflation as the deterministic FORM of "log" (#2).

**Why retain it.** It contributes the single cleanest *correct* statement of what the answer's
"log" must be: the probe shows the house **exactly saturates** `√n·√(2 ln N)` (concentration
κ = M²/rms² ≈ 2 ln N in every instance, zero slack). The periods are *maximally sub-Gaussian*. This
isolates the prize to **one b-sensitive deterministic claim: balance `κ_b ≤ 2 ln N` for the binding
b** — the BGK wall in geometric clothing, but a *clean named target* with the constant pinned.

**Sharpest next probe.** Test whether κ_b for the *binding* b is controlled by a **deterministic
lattice quantity other than the energy** — specifically the **covering radius vs successive minima
of the b-twisted sublattice** `{x ∈ Z[ζ_p] : Tr(b·x·ζ̄) structured}`. If a transference inequality
on a *b-dependent* sublattice (not the b-blind full Z[ζ_p]) gives κ_b ≤ 2 ln N, it escapes the
b-blindness kill. Prediction: fails because the b-twist is an isometry of Z[ζ_p] (Galois), so the
sublattice geometry is b-invariant — but this is worth one explicit check, as the *isometry* claim
is the exact load-bearing step and has not been probed directly.

### LEAD 3 (longshot) — Gauss-sum cocycle, the ONE structured-prime crack (#3).

**Why a sliver remains.** The full-rank kill is prime-independent for *generic* m. But the prize is
at **2-power m = 2^128**, and Hasse-Davenport gives extra relations *only at composite/2-power
character orders*. The probe used non-Fermat primes. The unprobed question: does the cocycle
relation matrix lose rank when the **2-adic valuation of m is maximal** (genuine 2-power tower),
giving a sub-m-dimensional variety specifically at the prize point? Prediction: no (the dossier's
"+4/+8 depth margin is a decaying norm-floor q^{2/n}, not √n growth" already suggests the 2-power
structure does not collapse dimension), but the rank computation **at maximal v₂(m)** is cheap and
has not been done.

---

## 4. DEEPEST CROSS-CUTTING INSIGHT — the sharpened necessary condition

The three original properties (b-sensitive, deterministic-archimedean, L∞) are necessary but
**demonstrably not sufficient**: discrepancy (#1), the Gauss-variety (#3), and the bootstrap (#4)
all pass all three and still die. The twelve deaths reveal a **fourth, refining property** that
every passing-but-dead mechanism violates:

> **(d) The mechanism must read the ABSOLUTE PHASES `{arg η_b}` (equivalently the absolute Gauss-sum
> phases `{arg g(χ)}`) — not merely moduli, phase-differences, energy, or the spectrum-as-a-set.**

Every dead mechanism fails (d) in one of two ways, and these are the *only* two ways:

1. **It reads only second-order data** (moduli |g(χ)| = √q, autocorrelation, energy `Σ|η_b|²`,
   RMS). The exact identity **p/m = n** then forces the target √(2n ln m) to be *literally* the
   free-phase EVT value — so any modulus/energy method's honest ceiling is either the trivial √p
   (phase-blind adversary, #5/#9/#11/#7) or the dead Gaussian-EVT saddle (#2/#8/#10). **Confirmed
   this session: tail@5σ is 3.5× heavier than Gaussian** — so even the EVT value is not an upper
   bound; the truth lives in the high cumulants the second-order data cannot see.

2. **It reads the absolute phases — but only by re-encoding the operator whose spectrum is `{η_b}`**
   (the circulant, the cyclic Gauss-polynomial, the transfer cocycle, the Jacobi cocycle). Then it
   is **circular**: the cocycle closure L_b^n = I (#12), the flat full-support DFT (#4), the
   full-rank cocycle (#3), the thin-orbit D* = M/n (#1) all collapse the mechanism back to M.

**The chasm is between (1) and (2):** there is no mechanism that reads absolute phase
**arithmetically** (sees that the specific phases `arg η_b` are *not* a worst-case alignment)
**without** building the spectral object. This is precisely why the wall is hard: the absolute
Gauss-sum phases are pinned *only* by Hasse-Davenport (phase-differences) and Stickelberger (p-adic
valuation) — **the archimedean absolute phase is unconstrained by all known algebraic relations**
(dossier A3 / Galois-house, q prime ⇒ f=1). A winning proof needs a **new arithmetic input that
constrains the absolute archimedean phase of a thin-subgroup Gauss sum** — exactly the
sum-product / effective-equidistribution / monodromy input the dossier names as the missing piece.

The two angles that got *closest* — discrepancy (#1) and Banaszczyk (#2) — are precisely the two
that came nearest to (d): discrepancy is the unique non-circular *form* of an absolute-phase L∞
statement (D*_b sees where the phases cluster), and Banaszczyk pins the *correct constant* of the
phase-balance (κ_b ≤ 2 ln N). Neither supplies the arithmetic; both reduce the prize to a single,
cleanly-stated absolute-phase claim. **That is the whole prize: one b-sensitive deterministic claim
that the binding coset's absolute phases are balanced (κ_b ≤ 2 ln N ⟺ D*_b ≤ C√(log m / n)),
provable only with a new equidistribution input that constrains absolute (not difference) phases.**

---

## 5. HONEST BOTTOM LINE

**No alien angle cracked effective √-cancellation. None even partially escaped the wall.** All
twelve confirm it, and every one reduces to exactly one of four dead mechanisms (moment/EVT, Weil
√q, circular-to-M, L²-conservation) or dies before the wall at trivial-n (total positivity). The
target √(2n log m) is *real* (M/target → ~0.9, confirmed n≤128) and is — by the exact identity
p/m = n — *identically the free-phase extreme-value value*, which is why every probabilistic,
modulus-only, or energy-based dress lands on it heuristically yet none can prove it (the true tail
is 3.5× heavier than Gaussian).

**Did anyone get genuinely closer?** Two contributions are worth keeping as *reformulations*, not
progress on the bound: (i) the discrepancy reduction `M ≤ C√(n log m) ⟺ D*_b ≤ C√(log m/n) ∀b` is
the only non-circular restatement passing all necessary conditions; (ii) the Banaszczyk saturation
`κ_b = M²/rms² ≈ 2 ln N` (zero slack, constant pinned) names the exact target as a balance claim.
Both are clothing, not cloth. The **one new theorem** produced is the dynamical kill: the cocycle
closure `L_b^n = I` proves the entire transfer-operator/dynamical-zeta class circular — a clean new
dead-ledger entry, not previously foreclosed.

**No larp.** Each mechanism was probed with exact coset-reduced numerics; each kill is tagged
(circular / reduces-to-moment / Weil-√q / phase-blind / L²-conservation / dies-before-wall) and
several are theorem-grade (full-rank cocycle, L_b^n=I, p/m=n, 24/24 decoupling falsification). The
prize remains open: one analytic inequality, thin-subgroup √-cancellation, at the Burgess barrier,
with a proven half-power gap — needing a genuinely new arithmetic constraint on the **absolute
archimedean phase** of thin-subgroup Gauss sums, which no current method supplies.

---

### EXECUTIVE SUMMARY

- **Survivors: NONE.** Twelve alien mechanisms (fermionic/SUSY, quantum-scatter, Bourgain-bootstrap,
  lattice-transference, total-positivity, Gauss-variety, Mahler-Galois, dyadic-decoupling,
  discrepancy, bootstrap-positivity, operator-dilations, dynamical-transfer) all fail. Each reduces
  to one of four dead mechanisms — **moment/EVT, Weil-√q, circular-to-M, L²-conservation** — or dies
  at trivial-n (total positivity) before reaching the wall.

- **Most-promising lead + next step: deterministic individual discrepancy (Koksma-Hlawka).** It is
  the *only* mechanism passing the full 3-property necessary condition without restating the target
  or using moments. It reframes the prize exactly as **`D*_b ≤ C√(log m/n)` for every b**. **Next
  step:** compute the continued-fraction / Ostrowski structure of the LCG multiplier `h = g^{(p−1)/2^μ}`
  and test whether `n·D*_b` for the worst coset tracks the partial-quotient sum `Σ a_i`
  *independently of M* (non-circular) or tracks M (circular). This is the single derivation in the
  assault not provably circular before running — though the dossier's "Korobov needs the full
  period" predicts it tracks M.

- **Sharpened necessary condition:** add **(d) the mechanism must read the ABSOLUTE archimedean
  phases `{arg η_b}` arithmetically — not moduli/energy/phase-differences (→ free-phase EVT value,
  since p/m=n), and not by re-encoding the period spectrum (→ circular-to-M).** No known algebraic
  relation (Hasse-Davenport, Stickelberger) constrains absolute archimedean phase; the prize needs
  a new sum-product / effective-equidistribution / monodromy input that does. The two angles that
  got closest (discrepancy, Banaszczyk transference) each reduce the prize to a single clean
  absolute-phase balance claim `κ_b ≤ 2 ln N` and supply the correct constant — but not the
  arithmetic.
