# Research plan: novel 2-power structures to bound the wraparound `W_r` (#444)

**Goal.** Bound `W_r` = #{(x,y)∈μ_{2^μ}^{2r} : p | (Σx−Σy)≠0} (the char-`p` excess), equivalently prove
`E_r(F_p) ≤ (2r−1)‼·n^r` to depth `r≈log p` at the prize prime `p ~ n·2^128 = 2^38·n^4` (`n=2^30`). This
is the SINGLE remaining open input; the entire reduction chain to it is formalized & proven (char-0
backbone: `_CharZeroStepRatioMonotone`; reduction: `_StepRatioMonotone`, `_CharPTransferDecomposition`).

**The non-reduction principle (proven by the whole campaign).** Everything that reduces does so via the
GENERIC rank-`n/2` obstruction (Minkowski/Evertse/Yu/large-sieve, all exponential in the cyclotomic unit
rank `n/2`). An escape MUST exploit the EXCEPTIONAL 2-power structure. This plan identifies those
structures and gives, for each, a concrete decidable question.

## Established facts (the foundation)
- `E_r(F_p)/Wick` DECREASES `0.94→0.11` (r=2..9, no char-0 ref ⟹ reliable): the bound holds with growing
  margin. char-0 monotonicity `G_0(r)≥0` PROVEN (r=2..5).
- The wraparound onset scales with `p/n^4`; the prize prime (`p/n^4=2^38`, very thin) is favorable.
- `v_2(W_r) ~ 2μ = 2·log_2 n` (machine: μ=4→7, μ=5→11): substantial 2-power symmetry divides `W_r`, but
  `W_r ≫ 2^{v_2}` so divisibility alone does NOT force `W_r=0`.
- `W_r` is NOT C-finite (no rational generating function) — a transcendence signal (modular?).
- The Frobenius/decomposition-group idea is REFUTED (`p≡1 mod n ⟹ p splits ⟹ σ_p=id`).

## The five 2-power structures (each with a decidable target)

### Structure A — the Clifford group / extraspecial 2-group `Cliff(2^μ)` ★ (highest value)
**Object.** `Aut(ℤ[ζ_{2^μ}])` contains the **Clifford group** (normalizer of the Pauli/Heisenberg group
over `ℤ/2^μ`), order `2^{O(μ²)}` — far larger than the dilation group (`2^{μ+1}`). It acts on the lattice
preserving the form; its invariants are 2-power-specific.
**Decidable target A1:** does the Clifford group preserve the wraparound condition `Σx≡Σy mod 𝔭`? (Dilation
& swap & negation do — giving `v_2(W_r)~2μ`. The Fourier/quadratic-phase Clifford gates mix coordinates;
TEST whether the wraparound set is Clifford-stable.) If YES, `W_r` is divisible by Clifford-orbit sizes
(`~2^{O(μ²)}`), forcing `W_r=0` whenever `W_r < |Cliff|` — a much stronger gap than the dilation `2^{v_2}`.
**Test:** enumerate the wraparound at a small bad prime, compute orbits under the Clifford generators
(Fourier `F`, phase `S: x↦i^{x²}`, CNOT). **Status:** UNTRIED. The genuine lead — fixes the refuted
Frobenius idea (vacuous cyclic group → non-vacuous geometric 2-group).

### Structure B — Barnes–Wall lattice `BW_{2^{μ−1}}` and its theta series
**Object.** `ℤ[ζ_{2^μ}]` with the trace form ≅ (scaling of) the Barnes–Wall lattice `BW_{n/2}` — the
*least generic* lattice (Clifford automorphisms, minimum `~2^{(μ−1)/2}`, extremal-adjacent theta).
**Decidable target B1:** the wraparound `W_r` ⟷ short-vector count of `𝔭·ℤ[ζ_n]`. Barnes–Wall short-vector
counts are governed by the Clifford-invariant theta, NOT Minkowski (generic). Is the count rank-independent?
**Caveat:** prize-scale `𝔭·ℤ[ζ_n]` has minimum `~p^{2/n}→1` (scaling may destroy BW structure). **Test:**
compute `θ_{𝔭·ℤ[ζ_n]}` low coefficients vs the BW theta. **Status:** UNTRIED.

### Structure C — Clifford-invariant CUSP forms of weight `n/4` ★★ (the deepest, most decisive)
**Object.** The theta series of `ℤ[ζ_{2^μ}]` is a modular form of weight `n/4`, split Eisenstein + cusp.
The cusp part = the rank-dependent "fluctuation" (the Deligne-bounded piece that makes generic theta
bounds reduce). BUT the theta is invariant under the Clifford group `Cliff(2^μ)`.
**Decidable target C1 (THE question):** is the space of **Clifford-invariant cusp forms of weight `n/4`**
ZERO (or polynomially-small)? If YES, the theta is Eisenstein-dominated ⟹ the representation/wraparound
count is the EXACT Eisenstein main term — a **RANK-INDEPENDENT** count ⟹ the prize. The Clifford group is
so large it may kill all cusp forms (the invariant subspace of `S_{n/4}` is trivial). **This is a concrete
question in modular forms with a finite-group symmetry — decidable by dimension formulas / trace formula on
the Clifford-fixed subspace.** **Status:** UNTRIED, the single highest-value target. (Low weight: `S_{n/4}=0`
trivially for small μ; the question is whether Clifford-invariance keeps it 0 as weight grows.)

### Structure D — dyadic tower relative-norm recursion
**Object.** `N: ℤ[ζ_{2^μ}]→ℤ[ζ_{2^{μ−1}}]` (degree 2, multiplicative) maps wraparound at level μ to μ−1.
**Decidable target D1:** the contraction factor of `W_r(2^μ)` in terms of `W_r(2^{μ−1})`. If `<1`,
telescopes to the `μ_2` base. **Machine caveat (this pass):** the onset scales differ across levels (`μ_n`
is good at the `μ_{2n}` prime), so a same-prime recursion is subtle; the tower must be taken at MATCHED
thinness `p/n^4`. **Status:** partially tested, onset-scaling complication identified.

### Structure E — the dilation / orbit-count divisibility (PROVABLE, but insufficient)
**Object.** `μ_n`-dilation acts on the wraparound (`Σ(ζx)≡Σ(ζy) ⟺ Σx≡Σy`), order `n=2^μ`.
**Result:** `v_2(W_r) ≥ μ` PROVABLE (dilation orbits), machine-confirmed `~2μ` (with swap+permutations).
**Verdict:** real & provable but `W_r ≫ 2^{v_2}`, so does NOT force `W_r=0`. The "obvious" 2-power symmetry;
the genuine escape needs the LARGER Clifford structure (A/C).

## The plan (ordered by value)
1. **★★ C1 — Clifford-invariant cusp forms of weight `n/4` = 0?** The decisive question. Attack via:
   compute `dim S_{n/4}^{Cliff}` for small μ (4,5,6) by the trace formula on the Clifford-fixed subspace,
   look for the pattern "0 for all μ". If 0 ⟹ rank-independent count ⟹ PRIZE.
2. **★ A1 — Clifford-stability of the wraparound set.** Enumerate wraparound orbits under the Clifford
   generators at a small bad prime; if Clifford-stable, get the strong `2^{O(μ²)}`-divisibility gap.
3. **B1 — Barnes–Wall theta of `𝔭·ℤ[ζ_n]`.** Low-coefficient computation; test rank-independence.
4. **D1 — matched-thinness tower recursion.** Recompute with `p/n^4` held fixed across levels.

## Honest status
The prize is reduced to ONE input (the wraparound bound), and the non-reduction MUST come from a 2-power
structure (A–E). The deepest, most decisive is **C1 (Clifford-invariant cusp forms = 0 ⟹ Eisenstein-
dominated theta ⟹ rank-independent count ⟹ prize)** — a concrete, decidable modular-forms question that no
prior approach has posed. This is the precise, novel, 2-power-specific target. NO fabricated closure; the
plan identifies exactly where a genuine escape lives and how to test it.

> Machine: `probe_dyadic_tower.py` (onset scaling, `v_2(W_r)~2μ`). The Clifford/cusp-form targets (A1/C1)
> need modular-forms / finite-group-invariant computation (next phase).
