# Reading list — the phase-equidistribution kernel (the sharpest open form of the prize)

The "New Mathematics" essay localizes the prize to ONE open object: the **horizontal (fixed-prime)
sup-norm equidistribution rate of the Gauss-sum phases** for the dyadic family `μ_{2^a}`. Everything
provable is on the magnitude/valuation side; the open content is entirely the phase side. This last
literature pass sharpens the gap precisely:

> **Vertical Sato–Tate (PROVEN, incl. effective versions) ≠ horizontal sup-norm (the PRIZE, OPEN).**
> Deligne/Katz prove the Gauss-sum phases `g(χ)/√p` equidistribute on the unit circle **as `q→∞`**
> (vertical: average over the field). The prize needs the bound at ONE FIXED prize prime, over the `m`
> frequencies `b` — a horizontal/individual sup-norm. Vertical equidistribution gives the `√(n log)` law
> only **on average / on the geometric mean** (matching Kowalski–Untrau, Habegger), never as the fixed-`q`
> sup-norm. That average-vs-individual gap IS the BGK wall, now in its phase formulation.

## The five papers for the kernel (the team should pull these)
1. **arXiv:2406.09633 — "An effective Deligne's equidistribution theorem"** (2024). The most recent
   *effective* (quantitative, with rate) vertical equidistribution. Check whether its rate can be made
   *uniform over the family* at fixed `q` — the one place a horizontal statement could leak out. HIGHEST
   priority: this is the closest proven result to the open kernel.
2. **arXiv:2207.12439 — "Equidistribution and independence of Gauss sums."** Joint/independence
   statements for Gauss sums — directly relevant to the *weighted sum* `Σ_b χ̄(b)g(χ)` cancellation
   (independence ⇒ the random-walk `√(m)` heuristic that gives `M~√n`).
3. **Katz, "Gauss Sums, Kloosterman Sums, and Monodromy Groups"** (Annals of Math Studies 116). The
   foundational monodromy computation; the source of the "n/4 free phase-DOF" (Katz monodromy floor) the
   fleet already hit. Read for whether the dyadic (2-power-order) family has *special, larger* monodromy.
4. **arXiv:2211.14702 — "Bilinear forms with trace functions over arbitrary sets, applications to
   Sato–Tate."** Bilinear/`b`-averaged forms — the structure of `M(n)=max_b|…|` is a sup over a bilinear
   form; this is the technology for converting average to individual over restricted `b`-sets.
5. **arXiv:2109.11961 — "Arithmetic Fourier transforms over finite fields: generic vanishing,
   convolution, equidistribution."** The Fourier-sheaf framework in which `S(b)=Σ_x∈μ_n e_p(bx)` is a
   trace function; generic-vanishing + convolution is the natural setting for a sup-norm (not average)
   bound.

## The precise question to ask each paper
Does it give an **individual** (not averaged-over-`q`) bound `max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log(p/n))`
for the **2-power subgroup at a fixed prime `p≡1 mod 2^a`**? If any does, *that is the prize* — feed me the
lemma and I formalize the consumer chain (the rest is proven, per the essay's magnitude side).

Honest note: as of this pass none does — all are vertical/average. The horizontal sup-norm for thin
2-power subgroups is the recognized open problem (BGK `n^{1−o(1)}`). Related: NEW-MATHEMATICS-essay.md §7d′.
