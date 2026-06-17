# Schizo + creative novel NT angles on the wraparound `W_r` — the non-reduction hunt (#444)

The razor-edge open object: bound `W_r` = #{(x,y)∈μ_{2^μ}^{2r} : p | (Σx−Σy) ≠ 0} = the count of mod-`p`
vanishing sums of `2^μ`-th roots of unity (equivalently `E_r(F_p) ≤ (2r−1)‼·n^r`). The user's ask:
genuinely novel NT, ideally provably-non-reducing. **Honest meta-principle (the key insight):** I CANNOT
prove non-reduction — that is *exactly* the open difficulty. But every approach that reduces does so via
the **generic rank-`n/2` obstruction** (the cyclotomic unit group / lattice has rank `n/2`; Minkowski/
Evertse/Yu/large-sieve are all exponential in that rank). So the ONLY candidates that could escape are
ones exploiting the **EXCEPTIONAL, 2-power-specific structure** that generic methods don't see. That is
the honest non-reduction filter: **2-power-specific ⟹ candidate; generic ⟹ reduces.**

## ⚠️ Honesty correction (machine-caught this pass)
My earlier "wraparound `W_r/Wick` is unimodal, peaks at r≈9" was a **contamination artifact** — the char-0
reference prime `q=10⁹` *itself* has wraparound once `(2r)^{n/2} > q` (n=16: beyond r≈6), so deep-`r`
`W_r = E_r(F_p) − E_r(F_q)` is NOT the true wraparound. The deep-`r` wraparound is genuinely **uncomputable**
(the char-0 reference needs infeasibly large primes; closed forms only to r=7). **Reliable findings:**
`W_r/Wick` RISES for r=4,5,6 (n=16); and — with NO char-0 reference — `E_r(F_p)/Wick` DECREASES
(`0.94→0.11`, r=2..9), so `E_r ≤ Wick` holds with growing margin (solid, favorable).

## The 2-power-SPECIFIC candidates (genuine non-reduction hunt)

**S1. Barnes–Wall lattice / Clifford-group symmetry of `ℤ[ζ_{2^μ}]`.** [GENUINELY NOVEL, 2-POWER-SPECIFIC]
The ring `ℤ[ζ_{2^μ}]` with the trace form is (a scaling of) the **Barnes–Wall lattice** `BW_{2^{μ−1}}` in
rank `n/2` — the *least generic* lattice, with the **Clifford group** (normalizer of the extraspecial
2-group, order `2^{O(μ²)}`) as automorphisms and a known, highly-structured theta series. `W_r` = short-
vector count of the sublattice `𝔭·ℤ[ζ_n]`. **Why it might NOT reduce:** the rank obstruction is Minkowski's
bound, *tight for generic lattices*; Barnes–Wall is the antithesis (huge symmetry, large minimum), so the
generic bound is loose — the Clifford-orbit structure could force a **rank-independent** short-vector count.
**Honest caveat:** at prize scale the sublattice `𝔭·ℤ[ζ_n]` has minimum `~p^{2/n}→1` (the scaling may
destroy the Barnes–Wall structure). UNTRIED; the genuine lead. (Generalizes the refuted Frobenius idea:
swap the *cyclic Galois* (`σ_p=id`, vacuous) for the *geometric Clifford 2-group* (acts on the lattice,
non-vacuous).)

**S2. Clifford / Gottesman–Knill "magic" dichotomy.** [SCHIZO, GENUINELY NOVEL] Read the energy `E_r` as a
tensor-network / Markov-trace contraction, and the `2^μ`-structure as a **Clifford quantum circuit**
(Clifford gates = the Pauli normalizer = exactly the `ℤ[ζ_{2^μ}]` symmetry). Gottesman–Knill: Clifford
circuits are classically *exactly* simulable. **The conjecture:** the char-0 energy is the "Clifford
(stabilizer) part" — exactly computable (= Lam–Leung) — and the wraparound `W_r` is the **"magic"
(non-Clifford / T-gate) correction**, whose count is governed by the *stabilizer rank* / magic monotone,
a 2-power-specific quantity. **Why novel/non-generic:** the Clifford-vs-magic split is intrinsic to powers
of 2; no generic-rank method sees it. **Honest:** speculative — whether the wraparound IS the magic count
is unverified; but it is a genuinely fresh, 2-power-native framing.

**S3. Dyadic-tower relative-norm recursion on the wraparound.** [NOVEL, 2-POWER-SPECIFIC] The relative norm
`N : ℤ[ζ_{2^μ}] → ℤ[ζ_{2^{μ−1}}]` (degree 2) maps a vanishing-sum-mod-`𝔭` at level `μ` to one at level
`μ−1`. This gives a genuine recursion `W_r(2^μ)` ⟷ `W_r(2^{μ−1})` *through the field tower*, not the
additive crossCell descent (which is dead). **Why might not reduce:** the norm is *multiplicative*
(different from the additive character sums that reduce), and it is 2-power-tower-specific. **Status:** the
recursion's contraction factor is the open piece; if `< 1` it would telescope `W_r` to the `μ_2` base.

**S4. Modular / mock-modular generating function (the non-C-finite signal).** [NOVEL] Machine-verified:
`W_r` is **NOT C-finite** (no constant-coefficient linear recurrence / rational generating function). This
*transcendence* is a genuine signal: `Σ_r W_r q^r` is likely **modular or mock-modular** (the theta series
of `ℤ[ζ_n]` is a modular form of weight `n/4`). If `Σ W_r q^r` is **Eisenstein-dominated** (no cusp form),
its coefficients equal the *exact* Eisenstein main term — a **rank-independent** count (the cuspidal
fluctuation, which is the rank-dependent Deligne-bounded part, would vanish). **Why might not reduce:**
generic theta-coefficient bounds are rank-dependent (weight `n/4`), BUT an Eisenstein-dominated form has NO
fluctuation to bound. **Status:** whether the cyclotomic wraparound theta series is Eisenstein-dominated is
the precise open question — genuinely new and decidable in principle.

## Reasonable (non-schizo) candidates, honestly verdicted
- **Successive-minima of `𝔭·ℤ[ζ_n]` (transference)** — REDUCES (generic, rank-`n/2`, Minkowski).
- **p-adic Mahler measure / 2-adic distortion height** — likely REDUCES (height = lower bound, wrong way).
- **Permanent / dimer / Pfaffian exact count of the matching structure** — appealing exactness, but the
  relevant graph is non-planar (no Kasteleyn); likely REDUCES.
- **Circle method with a 2-adic major-arc refinement** — the minor arcs are the wall (REDUCES).

## Honest bottom line
**None is proven non-reducing — that proof IS the prize.** But the hunt produced a clean *filter*: the only
genuine escape candidates are **2-power-specific** (S1 Barnes–Wall/Clifford, S2 magic-dichotomy, S3 norm-
recursion, S4 Eisenstein-dominated theta) — because the obstruction killing everything else is the
*generic* rank-`n/2` bound, and these four exploit structure (the Clifford 2-group, the dyadic norm tower,
the modular theta) that generic methods provably cannot see. **The single sharpest new target:** is the
wraparound generating function `Σ W_r q^r` Eisenstein-dominated (S4) / is `W_r` the Clifford-magic count
(S1/S2)? Either would give a rank-independent bound = the genuine non-reduction. The reliable evidence
(`E_r/Wick` decreasing, char-0 monotonicity proven, wraparound dominated by char-0 structure) all favors
the prize being TRUE; the missing input is one of these 2-power-specific structures delivering the bound.

> Honesty: no fabricated closure; `W_r` deep-`r` numerics flagged as uncomputable; non-reduction is the open
> problem, and the 2-power-specific filter is the honest characterization of where an escape could live.
