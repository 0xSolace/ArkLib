# Pinning δ* Through Every Face: Consolidated State of Proof (#444)

*State-of-proof census across all faces of the prize, 2026-06-21. Built by the `pin-deltastar-any-face`
workflow (the synthesis agent crashed on a 529; this is the editor-assembled census + the new Form-D
machinery I verified and committed). Every "proven" is machine-checked axiom-clean
(`[propext, Classical.choice, Quot.sound]`). The open core is the same wall through every face; this
document says exactly what is proven on each face, the single missing lemma, and which face is closest.*

---

## 0. The one-line state

`δ*` reaches the window interior **iff** `M=max_{b≠0}|η_b| ≤ C√(n log m)` (μ_n = 2^a-th roots, p~n^4,
m=(p-1)/n). Proven through every face that the open core is **one object**: the char-p wraparound
energy `W_r` at depth `r≈log p`. Two faces are *concretely pinned* (the ceiling); the open core is
*reduction-complete* on six faces, all bottoming at the same wall.

## 1. The faces, what is proven, the single missing lemma

| Face | Proven (axiom-clean) | Single missing lemma | Status |
|---|---|---|---|
| **A** Wick moment `E_r≤(2r-1)!!nʳ` | exact recursion `E_{r+1}=n·E_r+cross_r`; **char-0 r-linear step now a THEOREM** (cumulant engine); `E_2=3n²-3n`; DC-subtracted `A_r=qE_r-n^{2r}`; energy→sup bridge | `CrossBoundedByWick`: `c_r≤1` at `r≈log p` (the char-p wraparound) | reduction-complete; **moment→sup half-power OVERSHOOT** (`K_max^{1/2}=n^{0.385}`) |
| **B** sum-product / BGK | **DILUTION THEOREM** (sum-product provably stalls at α=1 at β=4); di Benedetto `n^{0.989}`, β=4 excluded boundary | — (proven DEAD as an escape) | **closed route**: tells you which surfaces are shut, forces non-tensor + phase-aware |
| **C/L** Λ(q)/Rudin–Pisier | reformulation-equivalent to A; finite-q Λ(q) escape CLOSED | identical to A | relabeling, no fresh handle |
| **D-DFT** Gauss-phase DFT | partial-DFT closed forms; `M=(√p/m)max_k|û(k)|`; `\|G\|=√p`; Katz/Deligne distributional shadow; KS→0 | effective **worst-case-uniform** sup `≤C√(m log m)` (effective vertical Sato–Tate at growing order) | **right language** (phase-aware); missing = effective worst-case equidistribution |
| **V** Wraparound Variance | **EXACT two-sided characterization** `A_k=qE^{c0}_k+q(W_k-mean)`; sandwich `M^{2k}≤A_k≤(q-1)M^{2k}`; both bounds from ONE bracket; lower floors `M≥√n,√3√n,√5√n,√7√n` LANDED | two-sided `\|W_k-mean\|≤δ` (i.e. `Var(W_k)=O(Wick)`) at `k≈log m` | **sharpest for the open core** (see §2) |
| **I** line-ball incidence | exact `lineIncidence=period L²` bridge; far-coset law; exact explosion-band values; L⁴ bridge | upper bound on far-line incidence = incidence-form of the wall | concrete for exact bands; asymptotic core = wall |
| **S** bad-side / KKH26 ceiling | **CEILING `δ*≤1-r/2^μ` proven UNCONDITIONAL** (KKH26 + Dirichlet prime supply); all bad families O(n)/q | a window-interior bad family > q·2^{-128} (none constructed) | **ceiling DONE** — δ* pinned from above |
| **C-cell** CellPackageSupply | entire consumer chain → `JohnsonDischargeStatement`; up-to-Johnson unconditional | `CellPackageSupply` (BCIKS20 §5 per-cell package production) | **most tractable UNBLOCKED face** — combinatorial, NO analytic wall, but Johnson-only |
| **D-Jacobi** (Form D, exact-sup) | char-0 backbone PROVEN (see §3); `prize_iff_turnover_le` under the edge-turnover model | Hermite-turnover at `k*=O(log p)` (recurrence leaves `b_k²=nk` early) | genuine relocation, right language (Deift–Zhou RH); exact-sup advantage **overstated** (see §3) |

## 2. The sharpest face for the open core: V (wraparound variance)

`_TwoSidedWraparoundCharacterization` proves **both** the upper and lower `√(n log m)` bounds reduce to
ONE object — `(W_k − mean)` — from a *single* `A_k` bracket: `upper_iff_wrap_le` (M≤C√ ⟺ not-too-positive),
`lower_iff_wrap_ge` (M≥c√ ⟺ not-too-negative), `twosided_from_variance` (a variance bound gives both via
Chebyshev). The lower floors are already landed (`M≥√n,√3√n,√5√n,√7√n`), and the lower direction is a
clean *not-too-negative* condition the floors partially supply. **Only the upper (not-too-positive)
direction is the bare Paley wall.** The remaining gap is `Var(W_k)=O(Wick)` at `k≈log m` — a quantitative
**arithmetic CLT** for short cyclotomic coincidences mod p. (Caveat: the relation graph is *not* sparse
at depth log p, so Stein/locality methods relocate — confirmed in the Paley-gap essay §IV.)

## 3. Form D (Jacobi-matrix / Hermite-turnover): char-0 backbone proven, exact-sup advantage tempered

The freshest face. The period moments are the Gaussian `N(0,n)` Wick moments, so the orthogonal-polynomial
recurrence should be Hermite. **Newly proven this campaign (axiom-clean):**
- the **Hermite recurrence `b_k²=nk`** — three independent ways: directly (`_FormDExactSupHermiteRecurrence.jacobiOffDiagSq_eq`), via Hankel determinant (`_FormDHankelHermiteTurnover.hermite_offDiagSq_eq`), via the **Toda string equation `b²(k+1)-b²(k)=n`** (`_AvJB_TodaStringHankelExact.toda_string_equation`);
- the **moment overshoot** `(specEdge)^r < Σ(g_b)^r` (`moment_strict_overshoot`) — *proves why face A loses the half-power*, unconditional;
- a Gaussian orthogonal-polynomial toolkit Mathlib lacks (`_FormDGaussOrthoPolyToolkit`: monic `gaussOP`, `derivative_gaussOP`, Stein IBP);
- the conditional exact-sup `M≤2√(n·k_max)` under a named `TopEigIdentity` hypothesis (`M_le_two_sqrt_of_topEig`), with `k_max=O(log p)` flagged as the residual.

**Honest caveat (from the census):** the exact-sup advantage is *overstated* by the probes — the `b_k` do
**not** cleanly follow `b_k²=nk` then sharply turn over; the empirical recurrence is messier, and the full
`topeig(J)=M=2max_k b_k` needs orthogonal-polynomial *spectral* machinery Mathlib lacks. So Form D is a
genuine **relocation** to a bounded, prime-discriminating invariant in the right language (Deift–Zhou
Riemann–Hilbert / equilibrium-measure edge), but the missing **turnover lemma `k*=O(log p)`** is the
deep-moment wall reorganized, not bypassed.

## 4. Where δ* is actually pinned, vs the open core

- **Pinned concretely (DONE):** the **ceiling** `δ*≤1-r/2^μ` (Face S, KKH26, Dirichlet-unconditional) and
  the up-to-Johnson reach (Face C-cell, `JohnsonListBound` unconditional). These pin δ* from above and to
  Johnson — the window *boundary*, not the interior.
- **The one unblocked incremental win:** `CellPackageSupply` (Face C-cell) — a self-contained combinatorial
  BCIKS20 §5 package-production lemma that needs *no* analytic wall, but only reaches Johnson, not the prize
  interior.
- **The open core (the $1M window-interior pin):** all of A/B/C/V/I/D-DFT/D-Jacobi collapse onto the char-p
  wraparound `W_r` at depth `log p`. Sharpest surface = **Face V** (two-sided, both bounds one object);
  best *language* = Face D-DFT / D-Jacobi (phase-aware, where the cancellation lives).

## 5. Open threads worth pulling (from the census)

1. **Face V upper direction** via a non-Stein second-moment bound on `Var(W_k)` (Stein relocates — locality
   fails at depth log p; needs a global/spectral variance method).
2. **Form-D turnover** via Deift–Zhou Riemann–Hilbert / equilibrium-measure edge analysis (the mature toolkit
   for recurrence-coefficient asymptotics) — the right machinery, not yet applied to the char-p perturbation.
3. **Effective worst-case vertical Sato–Tate** (Face D-DFT) — the gap between Katz's distributional
   equidistribution and the needed uniform-effective sup.
4. **CellPackageSupply** (Face C-cell) — the unblocked combinatorial win (Johnson-only, but real and
   formalizable today).

## 6. Honest verdict

Every face's open core is the same char-p wraparound wall at depth log p — now proven from B (dilution) to
be unreachable by sum-product, and proven from V to be a single two-sided variance object. The char-0
backbone of the exact-sup Form D is newly proven (Hermite recurrence 3 ways + overshoot + Toda/Hankel). The
prize remains open; the sharpest attack is Face V's not-too-positive direction (= the bare Paley wall), and
the best fresh *language* is Form-D's Riemann–Hilbert edge — but the exact-sup shortcut does not, on honest
inspection, bypass the wall. No QED is faked; δ* is pinned at the ceiling/Johnson boundary, open in the
interior.
