# The irreducibility theorem — rigorous form, after adversarial correction (2026-06-17)

Goal: prove the prize floor's IRREDUCIBILITY rigorously (= "just as good" as proving it). Three senses, each
adversarially stress-tested against the in-tree artifacts. Two of my first-draft claims OVERCLAIMED and are here
CORRECTED into rigorous form. Honest scope stated for each. This is NOT a proof the prize is unsolvable; it is a
rigorous characterization of its exact difficulty + a rigorous method-class barrier.

## SENSE A — meta-status (CORRECTED: "open & concrete", NOT "unprovable")
FLOOR-NT = `M(n)=max_{b≢0}|Σ_{x∈μ_n}e_p(bx)| ≤ C₀√(n log m)`.
- **At a FIXED explicit `C₀`:** `∀p ∀n=p^{1/4} ∀b: |S(b)|² ≤ C₀²·n·log m` is **Π₁** (a universal over integers with a
  decidable matrix — the sum is an algebraic integer, the inequality decidable). A true Π₁ sentence is provable in
  PA. So at fixed `C₀`, IF true THEN provable-in-principle — clean.
- **With existential `C₀`:** `∃C₀ ∀p∀n∀b …` is **Π₃**; truth does NOT formally force ZFC-provability.
- **CORRECTION (drop the earlier "not provable"):** for a Π₁ statement "false ∧ not-provable" is contradictory (if
  false, the negation is a true Σ₁ with a counterexample certificate, hence provable). Honest wording: **"concrete
  arithmetic (Π₁ at fixed C₀), currently OPEN, with NO basis for an independence/undecidability claim."** Asserting
  Sense-A undecidability is unfounded; I do not claim it. (This is why "irreducible" ≠ "undecidable" here.)

## SENSE B — the magnitude/phase decoupling barrier (CORRECTED: NOT "rank-1"; rigorous via DIRICHLET UNIT THEOREM)
First draft claimed "the product formula is the ONLY archimedean↔p-adic coupling, rank 1." **That is FALSE** — there
are further couplings (reflection `τ(χ)τ(χ̄)=χ(−1)q`; trace identity `Σ_σ|σ(β)|²=(n/2)·w` for antipodal-free signed
sums, in-tree `_wf5M2`; the Gross–Koblitz Γ_p-unit, in-tree `_GrossKoblitzPhaseNoGo`). The rigorous theorem is:

> **THEOREM (valuation-class barrier).** Let the field-arithmetic input of a proof be a functional of `α∈ℤ[ζ_n]\{0}`
> that depends ONLY on the ideal `(α)` — equivalently on the valuations `(v_𝔭(α))_𝔭` (this is the precise sense of
> "p-adic/cohomological/Stickelberger/crystalline-valuation input"; it is invariant under `α ↦ uα`, `u` a unit).
> Then such input determines `|N(α)| = ∏_σ|σ(α)|_∞` but leaves `max_σ|σ(α)|_∞` undetermined: by Dirichlet's unit
> theorem the units form a lattice of rank `r₁+r₂−1 = φ(n)/2 − 1`, and multiplication by units moves the vector
> `(log|σ(α)|)_σ` freely within the hyperplane `{Σ_σ x_σ = log|N(α)|}`. Hence no valuation-class functional can
> bound `M(n)` below the trivial norm-derived bound.

*Proof:* the ideal `(α)` fixes `α` up to a unit; Dirichlet gives the unit log-lattice of rank `φ(n)/2−1` spanning
the trace-zero hyperplane of the archimedean log-vector; the sup is a non-constant functional on that hyperplane,
so it is not fixed. ∎ **This IS rigorous** (Dirichlet unit theorem), under the explicit unit-invariance hypothesis.
- **Honest scope:** covers valuation-class methods (the entire cohomological / Stickelberger / Newton-polygon
  column — the in-tree bricks `_wf5M2`, `_wfA08`, `_wf5M1` are instances). It does NOT cover **phase-aware p-adic
  methods** (the Gross–Koblitz Γ_p-UNIT is finer than the valuation); for those the in-tree evidence is a χ²
  uniformity test on the 2-power phases (EVIDENCE, not a barrier theorem). So: rigorous no-go for the valuation
  column; the phase column is only empirically refuted. Free dimension is `φ(n)/2−1` (conjugation collapse), not `φ(n)−1`.

## SENSE C — reduction-completeness (CORRECTED: granular biconditional to INCIDENCE BUDGET; the M(n) step is lossy + named)
First draft claimed "floor ⟺ FLOOR-NT, exact biconditional." **Overclaim.** The honest in-tree status:
- **PROVEN, axiom-clean (a genuine biconditional, but GRANULAR):** `δ* ⟺ incidence-budget`
  (`OpenCoreConverse.deltaStar_iff_incidence_budget`): forward `worstCaseIncidence_pin` gives `δ ≤ δ*`; converse
  `worstCaseIncidence_of_lt_mcaDeltaStar` needs `δ < δ*` (strict) and budget `E=⌊q·ε*⌋`. So it is exact **up to the
  `<`/`≤` sSup boundary and `⌊·⌋` rounding** — a qualitative/granular equivalence, NOT exact-at-the-edge.
- **The step incidence-budget → the SCALAR `M(n)` (= FLOOR-NT) is NOT a proven biconditional.** It is:
  (i) **one direction FLOOR-NT ⟹ floor, LOSSY:** `M(n)` (an L∞ bound) → energy `Σ‖η_b‖^{2r} ≤ q·M^{2r}` → incidence,
      with a moment `min_r` over `r≈log q`, losing a **`√log` factor and constants** (gives `B ≤ √(2n ln q)`).
  (ii) **the converse floor ⟹ FLOOR-NT reduced to ONE named unproven `Prop`** (`PrizeEquivalence.ConverseRealizer`):
      the converse forces `I_u(δ)≤q·ε*` per stack, but extracting the scalar `M(n)` needs an EXACT worst-word
      realizer; the only loss-free Fourier bridge (`lineIncidence_period_sum`) collapses to the principal `η₀=|G|`
      and is BLIND to the non-principal `η_b` (b≠0) that `M(n)` is built from. Only the L² half
      (`incidence_l2_eq_period_l2`) is available. So the converse is reduced to `ConverseRealizer`, stated-not-proven.
- **CORRECTION (wording):** say **"the prize is reduction-COMPLETE for the incidence-budget (granular biconditional,
  PROVEN), and CONDITIONALLY/qualitatively equivalent (up to `√log` and constants, modulo one named realizer
  `ConverseRealizer`) to the thin-subgroup sup-norm FLOOR-NT."** NOT "exact biconditional floor ⟺ FLOOR-NT."

## The honest IRREDUCIBILITY THEOREM (assembled, with exact scope)
**Theorem (rigorous irreducibility, corrected).**
1. (Meta) FLOOR-NT is concrete arithmetic (Π₁ at fixed `C₀`), currently open; no basis for undecidability.
2. (Reduction-completeness, PROVEN axiom-clean) `δ* ⟺ incidence-budget` granularly; and FLOOR-NT ⟹ floor (lossy by
   `√log`); the converse is reduced to the single named `Prop` `ConverseRealizer`.
3. (Method-class barrier, PROVEN via Dirichlet) no valuation-class functional bounds `M(n)` (free dim `φ(n)/2−1`);
   the phase column is empirically (not provably) flat.
4. (Literature) `M(n) ≤ C₀√(n log m)` for `μ_n` of order `p^{1/4}` is recognized-open, best `n^{1−o(1)}` (BGK).

**Honest reading:** the prize is reduction-complete for a recognized open NT problem, AND the dominant proof-method
column (valuations/cohomology) is provably insufficient. This is "irreducibility" in the rigorous Sense-B+C form:
the prize is no easier than thin-subgroup √-cancellation, and the main toolkit provably cannot crack the latter via
valuations. It is NOT a proof that no proof exists (Sense A, false), and it is NOT an exact biconditional (the M(n)
step is lossy + one named realizer).

## What would make it fully formal (the honest remaining Lean work)
- The Dirichlet-unit valuation-class barrier (Sense B) is a clean, self-contained theorem FORMALIZABLE in Lean
  (Mathlib has Dirichlet's unit theorem + `NumberField.Units`). This is a genuine new shippable brick.
- The granular biconditional `δ* ⟺ incidence-budget` is already axiom-clean in-tree.
- `ConverseRealizer` remains the one named unproven `Prop` (the exact-worst-word extraction); discharging it
  unconditionally needs the non-principal `η_b` Fourier bridge that is exactly the open sup-norm content.

## Scope honesty (one line)
This proves: prize ≡ (granularly) a recognized open NT problem + valuation-methods provably insufficient. It does
NOT prove: the prize is undecidable, or that NO method can prove the floor (phase-aware methods are only
empirically refuted), or an exact biconditional. Those overclaims were caught and removed. Tools: adversarial
rigor agent (found all 3 corrections vs in-tree OpenCoreConverse/PrizeEquivalence/_wf5M2/_GrossKoblitzPhaseNoGo).
Related: docs 25 (first-draft barrier), 23 (capstone), 26–27 (the 200-angle sweep + rank-1 heuristic now corrected).
