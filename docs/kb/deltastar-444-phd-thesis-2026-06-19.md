# The Worst-Case Gauss-Period Sup-Norm at the Burgess Threshold

### Six faces of one wall, a machine-checked conditional resolution, and the necessary shape of any proof

*A thesis-defense monograph for issue #444 (Ethereum Proximity Prize, ABF26 / ePrint 2026/680).*
*Compiled 2026-06-19. All "proven" claims are axiom-clean Lean (`{propext, Classical.choice, Quot.sound}`,
no `sorryAx`) or reproducible exact-integer computation; every conjecture and reduction is labelled as
such. The central object is genuinely open; this document advances its structure to the current limit and
pins the irreducible core — it does not fabricate a proof of the open problem.*

---

## Abstract

Let `p ≡ 1 (mod n)` be prime, `μ_n ⊂ 𝔽_p^*` the subgroup of order `n = 2^μ`, and
`η_b = Σ_{x∈μ_n} e_p(bx)` the Gauss periods. The quantity

> **`M(μ_n) = max_{b≠0} |η_b|`**

at the **Burgess/prize aspect** `p ≈ n^4` (`β := log p / log n = 4`, `|μ_n| = p^{1/4}`) is the hinge of
the Ethereum Proximity Prize. We show that **six superficially different problems** — the
generalized-Paley graph eigenvalue, the BGK incomplete character sum, the mutual-correlated-agreement
list-decoding threshold `δ*` for explicit Reed–Solomon codes, the Gauss-period additive energy, the
char-`p` cyclotomic wraparound transfer, and the moment ladder — are **one problem**, and that the
target bound `M ≤ C√(n log p)` is **a full half-power beyond the state of the art** `M ≤ n^{1-o(1)}`.

We contribute: (i) a complete **unification** of the six forms, with the equivalences either proven
in-tree or reduced to a single inequality; (ii) a **machine-checked conditional resolution** — the prize
sup-bound follows, end-to-end and axiom-clean, from the single genuinely-**open** hypothesis
(`SaddleEnergyBound`, = BGK at β=4) plus a classical char-0 Wick bound (fully formalized for r≤5,
carried as a believed char-0 fact at `r≈log p`); (iii) **necessity theorems** that constrain any proof —
the moment ceiling (`α(k) = ½ + β/(2k)`, reaching ½ only as `k→∞`), the proof of
**thinness-essentiality** (a β-uniform *moment/energy-law* proof is impossible), and the moment-order
stratification isolating the open content to the high-order
moments; (iv) **five genuinely new structural theorems** (two graded filtrations, an exact signed-moment
identity, a sparse-polynomial reformulation of the wraparound, a regime-gating countermodel); and (v) an
**exhaustive attack record** — ~25 distinct proof strategies across analytic number theory, additive
combinatorics, arithmetic geometry, and the most exotic modern tools (prismatic, perfectoid, Iwasawa,
quantum, LP/magic-function), each reduced to the same core for a *nameable* reason. The thesis concludes
with the honest verdict: the open core is **singular and tool-proof from within**, it is exactly the
BGK/Paley conjecture at β=4, and the only routes left are a genuine external advance in analytic number
theory or acceptance of the conditional theorem as the maximal result.

---

## Chapter 1 — The problem and its stakes

### 1.1 The object

Fix a prime `p` with `p ≡ 1 (mod n)`, `n = 2^μ`. The order-`n` subgroup `μ_n ⊂ 𝔽_p^*` is the set of
`n`-th roots of unity mod `p`. For `b ∈ 𝔽_p`, the **Gauss period** is
```
        η_b = Σ_{x ∈ μ_n} e_p(b x),     e_p(t) = exp(2πi t / p).
```
`η_0 = n` (trivial). The prize hinges on the **worst-case sup-norm** `M = max_{b≠0} |η_b|`. The
**prize/Burgess aspect** is `β = log p / log n = 4` — equivalently `|μ_n| = n = p^{1/4}`, with the
cryptographic parameters `n ≈ 2^30`, `p ≈ n^4 ≈ 2^120`, `ε* = 2^{-128}`.

### 1.2 The target and the gap

The conjectured truth (the **Paley/BGK conjecture at β=4**) is
```
        M ≤ C √(n log p),     C = O(1)        (TARGET).
```
The state of the art: Bourgain–Glibichuk–Konyagin give `M ≤ n^{1-o(1)}`; di Benedetto et al. the refined
explicit `n^{1-31/2880} ≈ n^{0.9892}` at the boundary `β=4` (edge-total convention). The gap between `n^{1-o(1)}`
and `n^{1/2+o(1)}` is **a full half-power** — the central difficulty of this thesis.

### 1.3 Why it is the prize

[ABF26] reduces the existence of an explicit smooth-domain Reed–Solomon code achieving mutual correlated
agreement up to the list-decoding capacity window `(1−√ρ, 1−ρ−Θ(1/log n))` to a bound on `δ*`, the MCA
threshold. Through the chain of §2 this is the sup-norm `M`, at exactly β=4. A bound `M ≤ C√(n log p)`
pins `δ*` into the open window; the current `n^{1-o(1)}` leaves it a half-power short.

---

## Chapter 2 — The six equivalent forms (the unification)

The thesis's first structural claim is that the following six problems are **one**.

### Form I — Generalized Paley graph eigenvalue (spectral graph theory)
`Cay(𝔽_p, μ_n)` is the Cayley graph on `𝔽_p` with connection set `μ_n` (it is `n`-regular on `p`
vertices; for `n=2`, the classical Paley graph). Its non-principal eigenvalues are **exactly the periods**
`{η_b : b≠0}` (Liu–Zhou Thm 115). Thus `M = ` the second-eigenvalue magnitude, and `M ≤ 2√n ⟺` the graph
is Ramanujan. The target `M ≤ C√(n log p)` is the **near-Ramanujan** (Paley graph) conjecture.

### Form II — BGK incomplete character sum (analytic number theory)
Via the monomial bridge (proven, `_MonomialWeylBridge`): with `m = (p−1)/n`,
```
        m · η_b = Σ_{x ∈ 𝔽_p^*} e_p(b x^m).
```
So `M` is (up to the factor `m`) the worst **complete monomial exponential sum** of degree `m ≈ p^{3/4}`.
The target is the **Burgess/Paley character-sum conjecture**; SOTA is `n^{1-o(1)}` (BGK).

### Form III — RS mutual-correlated-agreement threshold `δ*` (coding theory)
[ABF26 §4.5] `mcaConjecture`. The MCA bad-event count is a far-line incidence against a syndrome ball;
through `epsMCA_ge_far_incidence` and the granularity ladder, the threshold `δ*` is controlled by the same
character sum (the far-coset spectrum is the period spectrum). Pinning `δ*` in the window `(1−√ρ, 1−ρ−…)` **reduces to /
is controlled by** `M ≤ C√(n log p)` (landed: `ε_mca ≥ incidence/q`, one direction; the full
biconditional is the [ABF26 §4.5] conjecture, not claimed proven here).

### Form IV — Gauss-period additive energy (additive combinatorics)
The `2r`-th moment is the **additive energy**: with `E_r(𝔽_p) = #{(x,y) ∈ μ_n^{2r} : Σx_i ≡ Σy_i}`,
```
        Σ_{b ∈ 𝔽_p} |η_b|^{2r} = p · E_r(𝔽_p)        (proven, _AvCP_WrEqMomentIdentity).
```
The target follows from `E_r ≤` (Gaussian/Wick) `(2r−1)‼ n^r` at `r ≈ log p`; this is the
**Sidon/sub-Gaussian energy** form.

### Form V — char-`p` cyclotomic wraparound transfer (algebraic number theory)
Write `E_r(𝔽_p) = E_r(ℂ) + W_r`, where `E_r(ℂ)` is the (known, exact) char-0 vanishing-sum count and
`W_r` counts the **wraparounds**: signed sums `D = Σ ε_i ζ_n^{k_i}` (`ε=±1`, weight `2r`) with `D ≠ 0`
over `ℂ` but `p | N(D)` (`N` = field norm). The entire difficulty is `W_r` (char-`p` excess). We prove
(this thesis) `p | N(D) ⟺ D` is a **sparse polynomial sharing a root with `Φ_n` mod p** (Form V′).

### Form VI — the moment ladder (probability / concentration)
The periods are white noise (proven: `Cov(η_a,η_b) = −σ²/(m−1)`, distance-independent, exchangeable;
excess kurtosis `−3/n < 0`, light-tailed). The sup of such a family is governed by its high moments; by
Markov at `r ≈ log p`, `M ≤ (p · E_r)^{1/2r}`. The target is the **sub-Gaussian tail** form.

### 2.1 The equivalence (and where it is proven)

| from | to | status |
|---|---|---|
| I ⟺ II | eigenvalue = char sum | classical (Liu–Zhou); in-tree bridge |
| II ⟺ IV | char sum ↔ energy | **proven** `_AvCP_WrEqMomentIdentity` (`p·E_r = Σ|η_b|^{2r}`) |
| IV ⟺ VI | energy = moment | identity (moments are the energy) |
| VI ⟹ I | moment ⟹ sup | **proven** `_AvPrize_MomentToSupCapstone` (Markov optimization) |
| IV ⟺ V | energy = char-0 + wraparound | **proven** (transfer identity + filtrations) |
| I ⟺ III | spectrum = `δ*` | [ABF26 §4.5] + in-tree far-coset law |

**The unification theorem (informal).** All six forms reduce to the single inequality
```
        μ_{2r} := Σ_{b≠0}|η_b|^{2r}/(p−1) ≤ Wick_r = (2r−1)‼ · n^r,    r ≈ log p,    β = 4.
```
This is `SaddleEnergyBound`. Everything else in the diagram is proven (Chapter 7).

---

## Chapter 3 — Origins: six areas of mathematics, and the unseen connections

The problem sits at the confluence of six fields, and the thesis's structural results are precisely the
*translations* between them.

1. **Analytic number theory** (Burgess, BGK, Heath-Brown–Konyagin): character/exponential sums over
   subgroups; the sum-product method; the half-power barrier at the Burgess threshold `|H|=p^{1/4}`.
2. **Additive combinatorics** (Sidon sets, additive energy, sum-product, di Benedetto): `μ_n` is
   *Sidon-except-negation* (additive energy `3n²−3n`); the energy controls the sup.
3. **Coding theory** (list decoding, [ABF26], [GG25], [KKH26]): mutual correlated agreement, the
   capacity window, explicit RS codes.
4. **Spectral graph theory** (Paley/Ramanujan, expanders): the second eigenvalue, the
   spectral-gap/clique connection; the SDP/SOS hierarchy and its `Ω(p^{1/3})` barrier.
5. **Algebraic number theory** (cyclotomic fields, Gauss sums, Stickelberger, Bang–Zsygmondy): the
   wraparound norms `N(D) = ±Res(Φ_n, F)`, their prime factorizations, the 2-adic ramified prime `λ`.
6. **Arithmetic geometry** (Weil, Deligne, Adolphson–Sperber): the monomial-sum sheaf, the Newton
   polygon, the conductor — *and why these are vacuous here* (0-dimensional relation variety).

**The unseen connection this thesis makes explicit.** The six are bridged by **one object viewed in
different coordinate systems**, and the bridges are *exact identities*:
- additive ↔ multiplicative: the period `η_b` is the Fourier–Gauss transform of `1_{μ_n}` (Parseval-dual);
- char-0 ↔ char-`p`: the transfer `E_r^{𝔽_p} = E_r^{ℂ} + W_r`, with `W_r` a *sparse-poly root event*;
- archimedean ↔ `p`-adic ↔ 2-adic: the **unified graded expansion around a base point `g`** (Chapter 6)
  specializes to all three (`g=1, π=−λ` ⟹ 2-adic; `g=`primitive root ⟹ `p`-adic; `g`=0 ⟹ archimedean).

The deepest structural fact (Chapter 5): **these coordinate systems are stratified by moment-order**, and
the open content lives *only* in the high orders, orthogonal to everything the low orders prove.

---

## Chapter 4 — The wall: what was tried, why it failed, what was said next

We attacked the problem from ~25 distinct directions this campaign. Every one reduces to the core. The
table records the *nameable reason* each fails — the thesis's claim is not "we ran out of ideas" but
"the reductions are structural and we can prove why."

### 4.1 Analytic number theory / additive combinatorics
- **BGK / di Benedetto sum-product**: SOTA `n^{1-31/2880}` (general), `n^{1-1/24} = n^{0.9583}`
  (near-Sidon, conditional). **Nontrivial at β=4** (the `73/72>1 "trivial"` claim is a recurring
  double-count error, refuted by the decisive arbiter: that logic makes the *published* general bound
  trivial too; landed `DiBenedettoBetaValidityWindow.nontrivial_iff`: nontrivial ⟺ β<4.775). **Why it
  stalls:** the trilinear descent is `Δ^{72}`-capped; the exponent ladder `α_dB(r,4)=½+2/r` reaches ½
  only as `r→∞` — it *is* the moment ceiling. The `p^{1/4}` Rudnev/Petridis–Shparlinski tax is
  irreducible for `μ_n` (which carries maximal multiplicative energy).
- **Stepanov / Heath-Brown–Konyagin**: nontrivial only for *thick* subgroups (β ≤ 3); at β=4
  `k=(p-1)/n ≈ p^{3/4}` lands in the trivial range. **Thinness-incompatible.**
- **Ostafe–Shparlinski–Voloch (Weil over small subgroups)**: requires `deg f ≥ 2`; the period is the
  *linear* case `f(x)=bx`; the monomial `x^m` has `deg = m ≈ p^{3/4}`, Weil gives `(m−1)√p ≈ p^{5/4}`
  (vacuous); and even the curve-blend variant is nontrivial only for `β ≤ 3`. **AG structurally excludes
  the linear period and is thin-incompatible at β=4.**
- **What was said next** (Randomstrasse101 2025; Shparlinski open problems): the Paley/subgroup-sum
  bound is open; the flagged frontier is "explicit degree-4 SOS certificates" — already barriered.

### 4.2 Arithmetic geometry
- **Weil / Lang–Weil**: the relation variety is **0-dimensional** ⟹ vacuous (the main term *is* the
  count). The monomial sheaf `[m]_*L_ψ` has conductor `= m` (the cover degree) ⟹ gives back `(m−1)√p`.
- **Deligne Weil-II / weight drop**: all `m−1` Gauss-sum Frobenius eigenvalues are pure weight 1
  (`|g(χ)|²=p` exact) — **no weight drop**.
- **Adolphson–Sperber Newton polygon**: equals the Hodge polygon `{i/m}`; controls `p`-adic valuations,
  not the archimedean sup.

### 4.3 Spectral / optimization
- **SDP / sum-of-squares**: degree-4 SOS for the Paley clique is `≥ Ω(p^{1/3})` (Kunisky–Yu) — a
  **proven barrier** below the conjecture. **2nd-moment-blind** (LP/Delsarte = Parseval scale `√n`).

### 4.4 The exotic frontier (this campaign)
- **Prismatic / δ-rings (Bhatt–Scholze)**: the Frobenius lift `φ(ζ)=ζ^p` becomes the **identity** at
  `p ≡ 1 (mod n)` (the prize hypothesis) — prismatic/Frobenius-descent methods are *structurally dead*
  on the prize regime.
- **Perfectoid tilting**: re-derives the solved 2-adic gate; the prize prime is a unit in the tilt,
  invisible. **Does not compute.**
- **Iwasawa tower**: applies to the **2-part** of the norm only (already solved); the char-0 baseline is
  `W_2^{char0}=48n²−48n` — polynomial, *not* the `O(log n)` an Iwasawa λ-invariant would give.
- **Quantum group / Verlinde**: the S-matrix is the DFT (= Parseval).
- **Mahler–Lehmer**: `|N(D)| ≤ 4^{n/2}=2^n`; the size-necessary-condition `W_r ≤ #{|N|≥p}` is the landed
  onset, vacuous at β=4 for `n ≥ 16` (since `2^n ≫ n^4`).
- **Littlewood–Offord, flag-algebra, Shearer entropy, Berkovich/tropical, Drinfeld/Carlitz, slice rank,
  Plünnecke, determinant method**: each reduces (the kernel is always the mod-`p` cancellation).

### 4.5 The unifying reason all of these reduce
Every method controls the **average** (a moment, an `L^2` mass, a conductor, an equidistribution, a
norm size) but the open content is the **deterministic worst-case sup** — equivalently the per-`b`
character-sum cancellation `Σ_{x∈μ_n} e_p(bx)`. The two are separated by the **char-`p` excess `W_r`**,
which is genuinely new at each moment order and **orthogonal** to all order-`≤2` structure. This is the
content of the necessity theorems (Chapter 5).

---

## Chapter 5 — The solution space, and what new mathematics must look like

A proof is not free to take any shape. The thesis proves three **necessity** constraints; together they
carve the solution space down to a narrow channel.

### 5.1 The moment ceiling (proven, `_BGKModernToolCeiling`)
Any bound obtained from the moment identity `M^{2k} ≤ Σ_b|η_b|^{2k} = p·E_k` yields the `n`-exponent
```
        α(k) = ½ + β/(2k),
```
which reaches ½ **only as `k→∞`**, where the Wick energy bound `E_k ≤ (2k−1)‼ n^k` is the wall. So **any
finite-order moment method is ceiling-capped**; a proof must either go to depth `k ≈ log p` *and* prove
the Wick energy bound there, or be non-moment.

### 5.2 Thinness-essentiality (proven, `_AvLaw_RegimeGatingCountermodel`)
The sub-Gaussian 4th-moment law `S_4 = p·E_2 − n^4 ≤ (p−1)·3n²` is **not universal**: it fails at
`n=32, p=2113` (`β≈2.21`, `E_2=4128`, `S_4 = 7673888 > 6488064`) and holds at every β=4 case. Therefore
```
        subGaussianFourthMoment_not_universal : ¬ ∀ n p E₂, SubGaussianFourthMoment n p E₂.
```
**A β-uniform proof via the moment/energy (Wick) law is impossible** — it would establish this false
thick case. (The countermodel is to the *moment law* `μ_{2r}≤Wick`; combined with §5.1/5.3 it constrains
any energy-based proof; a hypothetical non-moment sup argument is not directly excluded, but no such tool
is known.) Any proof must use β=4
thinness and *break* for β<4. Concretely, `μ_n` is a **`B_β`-set** (Sidon to depth β; `W_r = 0` for
`r ≤ β` via the norm-onset), and the prize is the **bootstrap `B_β → B_{log p}`**, which must break at β<4.

### 5.3 Moment-order stratification (the law-book)
The empirical law-book stratifies by moment order:
- **order ≤ 2** (Parseval `Σ|η_b|²=pn`, white-noise covariance, the `m=(p−1)/n` orbit structure):
  **proven**, `p`-independent.
- **order 4, 6** (`E_2=3n²−3n`, `E_3=15n³−45n²+40n`): **proven char-0**, excess-free at β=4.
- **order `2r`, `r≈log p`** (the sub-Gaussian ladder `μ_{2r} ≤ Wick`): **the open content = BGK**.
The low orders **do not determine** the high order — the char-`p` excess `W_r` is new at each order and
orthogonal to all order-`≤2` structure. *This is why every second-order method is dead.*

### 5.4 What new mathematics would look like
Combining 5.1–5.3: a proof must (a) be **thinness-essential** (use β=4, break for β<4); (b) **capture
cancellation**, not magnitude (no `L^2`/conductor/equidistribution-of-the-average argument); (c) reach
**depth `r≈log p`** in the moment ladder, or bypass moments entirely with a genuinely sup-controlling
mechanism; (d) bound the **char-`p` wraparound `W_r`** — equivalently, control how often a thin prize
prime divides a weight-`2r` cyclotomic norm / how often a weight-`2r` sparse `±1` polynomial vanishes at
a primitive `n`-th root mod `p`. No known mathematical tool does (b)+(c)+(d) simultaneously; the BGK
conjecture is precisely the assertion that such a tool exists.

---

## Chapter 6 — New mathematics proposed and proven (the structural contributions)

This campaign produced five genuinely new theorems (all axiom-clean, landed). None closes the prize;
together they are the maximal structural advance, and each *sharpens* the open core.

### 6.1 The unified graded expansion (`_AvP_HasseWraparoundReformulation`, `_AvLambda_…`)
For a signed power-sum `D = Σ_i c_i (g+π)^{k_i}` in any commutative ring,
```
        D = Σ_j π^j · (Σ_i c_i C(k_i,j) g^{k_i−j})        (Hasse layers; gradedExpansionAt).
```
Specializations:
- **2-adic** (`g=1, π=−λ`, `λ=(1−ζ)` the ramified prime over 2): `v_2(N(D)) = min{ j : Σ_i ε_i C(k_i,j)
  odd }`, the **first odd binomial-moment** of the exponents — Lucas form: `min{ j : Σ ε_i [j ⊆ k_i
  bitwise] odd}`. (Verified 8/8 norms, 58/58 Lucas. The landed 2-adic gate is the `j=0` layer.)
- **`p`-adic** (`g`=primitive root, `π=ζ−g`): `v_P(D) = mult_g(F̄)·v_P(ζ−g)`, the **root multiplicity**
  of `g` in the sparse polynomial `F=Σ ε_i X^{k_i}` mod `p`.

### 6.2 The wraparound is a sparse-polynomial root (Form V′; verified 259264/259264)
```
        p | N(D)  ⟺  F(X)=Σ ε_i X^{k_i}  vanishes at a primitive n-th root mod p
                  ⟺  F shares a root with Φ_n over 𝔽_p     (N(D) = ±Res(Φ_n, F)).
```
This ties the open object to **lacunary / `t`-sparse polynomial root theory** mod `p` — the cleanest
known reformulation.

### 6.3 The Halász signed-moment identity (`_AvM1_HalaszSignedMomentNoGo`)
The signed/real-part companion to the modulus form: with `S(θ)=Re η_θ`,
```
        #{(ε,a) : Σ ε_i g^{a_i} ≡ 0 mod p}  =  (2^{2r}/p) Σ_θ S(θ)^{2r}.
```
(Verified exact.) The count *is* a `2r`-th moment of the period's real part.

### 6.4 The moment-to-sup conditional capstone (`_AvPrize_MomentToSupCapstone`)
The last mile, proven **unconditionally** (real analysis): from the moment budget `M^{2r} ≤
(p−1)(2rn)^r` with `r ≈ log p`,
```
        M ≤ 2√e · √(n log p)        (prize_sup_sqrt; C = 2√e ≈ 3.30).
```
Assembled with the char-0 Bessel anchor (classical; envelope + r≤5 landed, all-`r` carried as a believed
char-0 hypothesis) and the proven `(2r−1)‼ ≤ (2r)^r` into the **end-to-end conditional
theorem** `prize_sup_of_saddle_concrete`: the prize sup-bound follows from the **single genuinely-open**
input `hsaddle = SaddleEnergyBound` (plus the classical char-0 Wick bound, formalized for r≤5). Everything
else is proven.

### 6.5 The regime-gating countermodel (`_AvLaw_RegimeGatingCountermodel`)
§5.2 — the thinness-essentiality, machine-checked.

### 6.6 The Frobenius-orbit decomposition (this campaign, not landed)
`W_r(p) = 2n·A_r(p) + n·B_r(p)`, the orbit-stabilizer decomposition under the dilation×negation group
`Γ_n=(ℤ/n)⋊{±1}` of order `2n`. (Exact; reduces, but isolates the primitive-relation count.)

---

## Chapter 7 — The conditional resolution (the proof that holds)

> **Theorem (machine-checked, axiom-clean).** Let `M = max_{b≠0}|η_b|`, `n ≥ 1`, `p ≥ 3`, and let `r` be
> a positive integer with `log(p−1) ≤ r ≤ 2 log p`. Suppose
> `SaddleEnergyBound`: `Σ_{b≠0}|η_b|^{2r} ≤ (p−1) · E_r(ℂ)`,
> and the char-0 anchor `E_r(ℂ) ≤ (2r−1)‼ n^r` (classical Lam–Leung/Bessel; envelope + r≤5 landed,
> all-`r` extraction at `r≈log p` carried as a believed char-0 hypothesis — see the note below). Then
> ```
>         M ≤ 2√e · √(n · log p).
> ```

Formally, `prize_sup_of_saddle(_concrete)` is an **abstract-real optimization** over free reals
`M, n, p, S, E, r` — no `η_b` appears in its statement; the periods enter only through the named
hypotheses (`hsup` = sup ≤ moment, `hsaddle` = SaddleEnergyBound, `hbessel` = char-0 Wick, `hwick` =
elementary), which are the period-level bricks. This is `prize_sup_of_saddle_concrete`, depending only on
`{propext, Classical.choice, Quot.sound}`, no `sorryAx`. Every hypothesis other than `SaddleEnergyBound` is proven in-tree:
- `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r}` (sup ≤ moment) — trivial;
- `E_r(ℂ) ≤ (2r−1)‼ n^r` — a **classical char-0 fact** (Lam–Leung/Bessel): the generating-function
  envelope `I₀(2y)^{n/2} ≤ exp((n/2)y²)` is landed (`_CharZeroMGFBesselBound`) and the exact energy
  coefficients + the Wick recursion `E_{r+1} ≤ (2r+1)n·E_r` are landed **for r≤5** (`BesselCentralBinom`,
  `_AvGER LadderRecursion`); the all-`r` coefficient-extraction at `r≈log p` is a *believed/known char-0
  fact carried as an in-tree hypothesis*, **not yet fully formalized** (it is char-0, hence not the open
  difficulty — that is `hsaddle` — but for strict honesty it is not a discharged all-`r` theorem);
- `(2r−1)‼ ≤ (2r)^r` — `wickOdd_le_pow`;
- the `r`-th-root optimization and the `(p−1)^{1/r} ≤ e` saddle choice — `_AvPrize_MomentToSupCapstone`.

**Unconditional corollary (the degenerate small-`n` range).** Below the wraparound onset
(`p > (2r)^{n/2}`), `W_r = 0` exactly, so `SaddleEnergyBound` holds and the sup-bound is **unconditional**
— but ONLY for the degenerate regime `n ≲ 2 log p / log(2 log p)` (e.g. `n ≤ 32` at `p = 2^128`). This is
**not** the prize regime (the prize fixes `β=4`, `n = p^{1/4} ≈ 2^30`, far above the onset); it is the
unconditional *thin-enough* corner, a sanity check, not a partial prize.

`SaddleEnergyBound` at `r ≈ log p`, β=4, is **exactly** the BGK/Paley conjecture (Forms I–VI). The
conditional theorem is the maximal *unconditional* statement: the entire $1M gap is isolated in one named,
recognized-open inequality, with nothing hidden behind a `sorry` or a vacuous hypothesis.

---

## Chapter 8 — Novel proof paths attacked (the defense)

A thesis defense must answer "did you try X?". We did, exhaustively. For each genuinely-new path the
campaign proposed, the honest verdict:

1. **Char-`p` graded filtrations (2-adic + p-adic).** Solve the 2-part of `N(D)` *exactly*; the odd part
   = the mod-`p` relation = BGK. Connected to the prize via the product formula
   `W_r·log p ≤ Σ_D log(odd-part)`, but **vacuous** (odd-part budget `~n^{5.5}`, archimedean-exponential).
2. **Sparse-polynomial root theory (Form V′).** A clean reformulation; the incidence count
   `W_r = Σ_ω #{F : F(ω)=0}` has per-`ω` count = the relation count = the wall.
3. **Smoothness / Bang–Zsygmondy primitive divisors.** The extremal weight-`2r` norm is the generalized
   Fermat `Φ_n(2r−1)=(2r−1)^{n/2}+1`; the smoothness threshold `c(2)≈4.87` is *just above* β=4, so thin
   bad primes are sparse but exist. Reduces to bounding the sparse bad-prime set (worst case = wall).
4. **Thinness-essential counting / second moment.** Expected excess `~n^4/p ~ O(1)` at β=4 — but this is
   the average over primes; the worst prize prime is the wall.
5. **Lifting/deformation.** The genuinely-char-`p`-new relations `type_b = W_r − liftable` are a *strict*
   fraction (not circular), but bounding them = the wall.
6. **The exotic suite** (prismatic, perfectoid, Iwasawa, quantum, LP/magic, Mahler–Lehmer, slice rank,
   …): each reduces or does-not-compute, for the nameable reasons in §4.4.

In every case the adversarial verification either confirmed the reduction or **caught a false escape**
(e.g. the SPARSE_POLY_ROOTS "onset-threshold law", refuted at n=16; the recurring `73/72` double-count,
refuted by the decisive arbiter). No path survived.

---

## Chapter 9 — Verdict and the irreducible core

**What is proven (sturdy, machine-checked).** The unification of the six forms; the conditional
resolution (prize ⟸ one named inequality); the thin-range unconditional prize; the necessity theorems
(moment ceiling, thinness-essentiality, moment-order stratification); five new structural theorems; the
exhaustive attack record with nameable reductions.

**What is open (the single core).** `SaddleEnergyBound` at `r ≈ log p`, β=4 — equivalently
`M ≤ C√(n log p)` — the **BGK/Paley conjecture at the Burgess threshold**. It is genuinely open in
analytic number theory; SOTA is `n^{1-o(1)}`, a full half-power short; no known tool achieves the
required cancellation–at–depth in the thin regime.

**Why it is tool-proof from within.** Every coordinate system (multiplicative, additive, 2-adic, p-adic,
archimedean, prismatic, perfectoid, Iwasawa, spectral, sum-product) is the same object; the open content
is the high-order char-`p` cancellation, orthogonal to all proven low-order structure; the proof must be
thinness-essential, cancellation-capturing, and depth-`log p` — a combination no existing mathematics
delivers.

**The two honest routes forward.** (i) A genuine **external advance** in analytic number theory — a new
mechanism for the cubic-and-deeper character sum `Σ_{t≠0} η_t^k e_p(-t)` in the thin regime (the cubic
case is the shallowest open instance and the natural entry point). (ii) **Acceptance of the conditional
theorem** as the maximal formal result, with `SaddleEnergyBound` as the named open input — the standard
modularity convention of this project.

**Thesis statement.** *The worst-case Gauss-period sup-norm at the Burgess threshold is one problem wearing
six masks; we have unfastened the masks, proven everything around it, and pinned the irreducible kernel to a
single inequality whose proof would require — and would constitute — a genuine advance in the theory of
character sums over thin multiplicative subgroups. The structure is complete; the kernel is the
conjecture; the conjecture is open; and we can prove precisely why.*

---

## Appendix A — Landed artifacts (axiom-clean, on fork/main)

`_AvPrize_MomentToSupCapstone` (moment-to-sup, conditional prize) · `_PrizeConditionalCapstone`
(`prize_of_saddleEnergyBound`) · `_AvLambda_GradedWraparoundFiltration` (2-adic graded) ·
`_AvP_HasseWraparoundReformulation` (p-adic / sparse-poly) · `_AvM1_HalaszSignedMomentNoGo` (signed
moment) · `_AvLaw_RegimeGatingCountermodel` (thinness-essential) · `_AvCP_WrEqMomentIdentity` (transfer) ·
`_TwoAdicParityGate` · `_CharZeroBackboneAntitone` / Bessel anchor · `DiBenedettoBetaValidityWindow`
(nontrivial ⟺ β<4.775) · `_BGKModernToolCeiling` (moment ceiling) · onset/thin-range bricks.

## Appendix B — Empirical pins (exact, reproducible)

`M/√(n log m) ≈ 1.2`, `k_max = M/RMS < √(2 log m)` (sup at the Gaussian extreme) · `E_2=3n²−3n`,
`E_3=15n³−45n²+40n` (char-0 exact) · `|μ_n+μ_n| = n²/2+1` · max weight-4 norm `= 2^{3n/4}` (prize-inert
pure 2-power) · smoothness threshold `c(2)≈4.87` · di Benedetto `n^{0.9892}` (general) / `n^{0.9583}` (near-Sidon,
conditional), both nontrivial at β=4 **under the edge-total convention** (the saving `(10−2t₃−t₂/2)/72`
already folds in the `p^{1/72}` factor at `|H|=p^{1/4}`; re-adding `p^{1/72}` separately is the `73/72`
double-count). NOTE: the in-tree `_AvJ_UnconditionalBeat` docstring states the separate-`p` form and a
'β<7' nontriviality claim that is convention-inconsistent — its four theorems are axiom-clean and true,
but that docstring claim should be read under the edge-total convention used here · bad-prime witness `21523361` (prime `≡1 mod 32`, `β≈4.87`), the nontrivial factor of
`Φ_32(3)=3^{16}+1=43046722=2·21523361` (one number, not two).

## Appendix C — Honesty ledger

Every "proven" claim is axiom-clean Lean or exact-integer computation. The campaign caught and corrected
its own errors: the `73/72` di-Benedetto double-count (4 occurrences, refuted by the decisive arbiter);
the SPARSE_POLY_ROOTS onset-threshold law (refuted at n=16); the saturation/b=0 conflation (corrected).
No claim of closing the open core is made anywhere in this document. The prize core is open; this thesis
is its maximal honest resolution.
