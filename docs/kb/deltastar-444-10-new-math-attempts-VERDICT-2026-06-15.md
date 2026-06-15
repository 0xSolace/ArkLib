# The 10 new-math attempts: ALL fall — and the deeper result is an INTRINSIC conservation law (#444, 2026-06-15)

The manifesto (`deltastar-444-new-math-manifesto-2026-06-15.md`) argued that every dead route sought
cancellation ON the n-domain (where `n<√q` forbids completeness), and that the new math must RELOCATE
the cancellation locus to (A) the parameter family, (B) the 2-adic completion, or (C) an information
functional. We attempted all three relocations across 10 never-before-tried angles. **Verdict: all 10
fall.** But they fall in a way that is *more informative than the manifesto predicted* — and that is the
real result.

## The 10 verdicts (each agent-attacked + adversarially verified; probes/Lean committed)

**(A) Parameter family.**
- **A1 Krawtchouk-as-trace-function / FKM sheaf — REFUTED.** The conductor of the Krawtchouk-weighted
  dual-code sheaf is NOT bounded; Deligne/FKM does not bite uniformly. (Initially flagged a survivor;
  killed on verification.)
- **A5 Terwilliger-algebra operator norm — REDUCES-TO-WALL, EXACTLY.** The Krawtchouk-weighted Bose–Mesner
  element `W=Σ_i K_w(i)A_i` is diagonal in the character basis with eigenvalue, restricted to the smooth
  dual code, **literally equal to the incomplete Gauss period `η_b`**. So the Terwilliger operator norm
  `= max_{b≠0}|η_b| = M(μ_n)` — the parameter/scheme object *is* the wall. (Axiom-clean brick
  `_a5_terwilliger_collapse.lean`: `terwilliger_reduces_to_wall`, `terwilliger_no_independent_gain`.)

**(B) 2-adic / p-adic completion.**
- **A3 2-adic Newton polygon — REFUTED** (vacuous relocation, 3 horns; the NP count does not beat Mann
  in the window).
- **A4 Amice/Iwasawa interpolation — REFUTED.** The tower period is a *b-independent p-adic UNIT*
  (power-sum gap lemma): its λ-invariant datum is **uncorrelated** with the archimedean sup. The 2-adic
  completion carries *no information* about `max|η_b|`.

**(C) Information / entropy functional.**
- **A2 generic chaining (route 54, the catalog's flagged-best) — REDUCES-TO-WALL.** The chaining metric
  entropy of the `u₀`-process is `Θ(log q)`; the multiplicative dilation orbit does NOT collapse it (the
  *additive* chaining metric is blind to the multiplicative structure). The `√log` is not absorbed.
- **A7 Croot–Sisask almost-periodicity — REFUTED.** `M/(2·avg)` grows like `√log(p/n)` — i.e. the
  Bohr-set forcing reproduces *exactly the floor's excess*, not a saving.
- **A10 entropy-compression — REFUTED + reduces-to-Johnson.** The entropy bound runs *backwards* (it
  lower-bounds the list); the only genuine gain is the antipodal/Mann boundary = Johnson.

**Other loci.**
- **A6 Schur–Siegel–Smyth trace problem — reduces-to-Johnson.**
- **A8 Bourgain–Gamburd multiplicative gap — REDUCES-TO-WALL.** The dilation action is **amenable** (no
  superstrong-approximation expansion); the affine block *is* the period.
- **A9 Kelley–Meka 2023 / PFR — REDUCES-TO-WALL** (energy/moment; KM is the wrong one-directional theorem;
  density-vacuity). Axiom-clean no-go `_A9KelleyMekaPFRNoGo.lean`.

## The deeper result: the wall is INTRINSIC, not merely "on the domain"

The manifesto said the answer might live off the domain. The attempts show something stronger: **every
faithful relocation's natural invariant either EQUALS `M(μ_n)` or is UNCORRELATED with it.**
- A5 (Terwilliger), A8 (dilation/affine block), A2 (chaining metric) — the relocated object *is* the period
  sup, reproduced exactly.
- A4 (p-adic unit), A10 (entropy backwards) — the relocated object is *orthogonal* to the period sup,
  carrying no information about its size.

This is a **conservation law sharper than the route-elimination meta-theorem**: `M(μ_n)` is not an
artifact of attacking the domain — it is the genuine invariant that every honest reformulation either
recomputes or misses. The cancellation locus *cannot* be relocated, because there is nowhere for it to go:
the parameter family's spectral object is the period (A5), the multiplicative action is amenable (A8), the
p-adic completion is a unit (A4), and the entropy/chaining functionals see only the average (A2/A7/A10).

## Honest meta-conclusion
No crack. But the 10 attempts mapped the **second boundary** the manifesto anticipated: the limit of what
relocating the cancellation locus can buy is *zero*, and we now know *why* — `M(μ_n)` is intrinsic. The
genuine open problem (the BGK/Paley sup-norm `M(μ_n) ≤ C√(n log(p/n))`) must be attacked *as itself*, with a
genuinely new analytic-NT input (effective sum-product / Stepanov-with-2-adic-auxiliary that no current
theorem supplies), not via any change of mathematical universe. Axiom-clean by-products this round:
`_a5_terwilliger_collapse.lean`, `_A9KelleyMekaPFRNoGo.lean`, the Tao-uncertainty→Chebotarev-minor reduction,
and the even/odd off-BGK-tower scope brick. DISPROOF_LOG updated for all 10.
