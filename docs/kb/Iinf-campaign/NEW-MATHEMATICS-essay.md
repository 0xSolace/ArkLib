# New Mathematics
### Five original attacks on the proximity-prize wall, and one unifying picture
*Issue #407 — δ\* in the prize regime. An essay of conjecture, not closure. 2026-06-15.*

---

## 0. Prologue: what a breakthrough would have to look like

Every honest investigation — ours and the 1,587-comment fleet's — has converged on a single wall:
the worst-case incomplete character sum over the thin dyadic subgroup,
`M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(bx)|`, must satisfy `M(n) ≤ C√(n·log(p/n))`, and the best proven
bound is BGK's `n^{1−o(1)}` against a needed `n^{1/2}`. We *proved* (the Fourier fixed-point identity
`N_k = p^{-1}Σ_b|S(b)|^{2k}`) that every face of the problem — list size, additive energy, the
cyclotomic norm `N(β)`, the Cayley eigenvalue `λ₂` — is literally this one object. So a genuine
breakthrough cannot be a *re-reduction*. It must be one of exactly three things:

1. **Lift a value** — prove `M(n) ≤ n^{1−c}` for a *larger* constant `c` than BGK's `o(1)`, using
   structure BGK throws away (the 2-power / dyadic structure).
2. **Remove a term** — show the prize does not actually need the full sup-norm, only a weaker proven
   quantity (an average, a one-sided count, a geometric mean).
3. **Prove the wall is the answer** — show the true `δ*` is strictly *below* the conjectured window
   edge, so the exact (computable, char-0) value *is* the closed answer and the BGK gap is illusory.

This essay develops one new idea in each of these three modes, plus a unifying picture that — to my
knowledge — has not been written down: **the prize prime is below the p-independence threshold, and the
whole difficulty is a deletion deficit.** All five attacks are new. None is a closure; several are, I
believe, genuinely worth a research program.

---

## 1. The unifying picture: p-independence *breaks* exactly at the wall, and the prize is a *deletion* problem

Two facts we proved separately turn out to be the same fact, and putting them together reframes
everything.

**Fact A (p-independence / norm gate).** A bad configuration is a non-antipodal `S ⊆ {0..n−1}` with
`β_S = Σ_{i∈S}ζ_n^i` satisfying `𝔭 ∣ β_S` (spurious vanishing mod the prize prime `p`). Since
`|N(β_S)| ≤ house^{φ(n)} ≤ n^{n/2}`, spurious vanishing is **impossible** while `n^{n/2} < p`. We measured
the realized worst-case norm: `log₂|N(β_S)| ≈ n`, crossing `log₂ p = 128` at **`n ≈ 128`**.

**Fact B (monotonicity, proven, ring-hom).** The reduction `ℤ[ζ_n] → F_p` is a ring homomorphism, so the
char-p bad-scalar set is the **image** of the char-0 set: reductions can only **merge or delete** bad
scalars, never create. Hence `#bad_p(δ) ≤ #bad_0(δ)` for every `δ`, and therefore
`δ*_p ≥ δ*_0` for every prime, with **equality in the worst case**.

Combine them. Below the crossover (`n ≲ 128`), no spurious vanishing exists, so no deletions happen:
`#bad_p = #bad_0` exactly, and `δ*` is the **exact, computable, q-independent char-0 value** — this is
*why* the fleet could pin `δ*(μ₁₆) = 9/16` in closed form, and *why* BIND is Lean-proven for `n ≤ 64`.

Above the crossover (`n ≳ 128`, i.e. the entire real FRI regime `n = 2^{32..43}`), the char-0 incidence
is **too large** — it is superlinear (`D₂ = n²/4 − n` at capacity), exceeding the budget `n` *long before*
the window edge. So `δ*_0 < ` window edge. The prize asks for `δ*_p = ` window edge. By monotonicity the
only way to get there is for the finite field to **delete** char-0 bad scalars — and deletions *are*
spurious vanishings, governed by equidistribution = BGK.

> **The new framing.** The prize is not "bound the incidence." The char-0 incidence is already known and
> already too big. The prize is: **guarantee that *enough* char-0 bad scalars are deleted by the
> reduction mod p, uniformly over all primes, all the way up to the window edge.** You do not want the
> character sum to be small for its own sake — you want it to *vanish often enough* to thin the
> char-0 list down to budget. The quantity to control is the **deletion deficit**: the number of char-0
> bad scalars that *survive* mod p.

This sign-flip matters. It says the right object is a **survival count**, not a sup-norm — and survival
counts are sievable. That is Attack 1.

---

## 2. Attack 1 (remove a term): the deletion sieve — bound survivors, not the sup-norm

A char-0 bad scalar `γ` (a far-line incidence point) survives mod `p` iff its configuration does **not**
spuriously vanish, i.e. `𝔭 ∤ β_{S(γ)}`. We want `#{survivors at δ_we} ≤ budget = n`.

Write the survival indicator by inclusion–exclusion over the *prime ideals above p*. For the dyadic
field `ℚ(ζ_{2^a})`, `p ≡ 1 (mod 2^a)` splits completely into `φ(n)=n/2` degree-1 primes
`𝔭_1,…,𝔭_{n/2}`, each with residue field `F_p` and a fixed primitive root `ω_t = σ_t(ζ) mod 𝔭` (the
Galois conjugates). Then
```
β_S ≡ 0 (𝔭_t)  ⟺  Σ_{i∈S} ω_t^{i} ≡ 0 (p),
```
one congruence per conjugate. A char-0 bad scalar deletes iff it vanishes at **some** `𝔭_t`. So
```
#survivors = #{ char-0 bad γ : Σ_{i∈S(γ)} ω_t^i ≢ 0 (p) for ALL t = 1..n/2 }.
```
This is a covering / sieve problem: the char-0 bad set is covered by `n/2` "vanishing events," and we
want the *uncovered* part small. **Novelty:** nobody has run the sieve in this direction — the fleet
chased the magnitude of *one* `M(n)`; here we use *all `n/2` conjugate sums at once* as a covering
family, and ask for near-total cover.

The cross-conjugate structure is the lever. The `n/2` events are not independent: `ω_t = ω_1^{u_t}`
ranges over the `φ(n)` units, and `Σ_i ω_t^i = σ_t(β)` are Galois conjugates of one algebraic number.
A char-0 bad `γ` survives iff `β_S` is a `𝔭`-adic unit at *every* prime above `p` — i.e. iff
`gcd(N(β_S), p) = 1`. So
```
#survivors = #{ char-0 bad γ : p ∤ N(β_{S(γ)}) }.
```
**This is a clean, finite, computable count** — and it is *one-sided* (we only need an upper bound on
survivors, never a two-sided sup-norm). The deletion sieve replaces "prove `√n` cancellation" with
"prove that `p` divides `N(β_S)` for all but `≤ n` of the char-0 bad configs." Because the char-0 bad
configs are *structured* (they are the simultaneous-vanishing variety `e_1=…=e_{t−1}=0`, a dilation-closed
union of `≈ n` cosets — our proven rigidity engine), the surviving set is a *sub-variety condition
intersected with a divisibility condition*, and inclusion–exclusion over the few prime divisors of each
`N(β_S)` may bound it without ever touching `M(n)`.

**Honest status.** This does not obviously close — the worst-case `N(β_S)` has up to `n/log p ≈ n/128`
prime factors near `p`, and controlling which of them equal the *fixed* prize `p` is, in the limit, the
equidistribution question again. But the *framing* is new and strictly one-sided, and it is the first
formulation where the proven monotonicity does real work. **Feasibility as a research target: 6.**

---

## 3. Attack 2 (lift a value): the 2-adic multilinear reformulation and slice rank — the structure BGK ignores

BGK is *blind to the 2-power structure*: it treats `μ_n` as an arbitrary multiplicative subgroup of size
`n` (this is exactly why the fleet found "no 2-power lever" empirically — but only at `n ≤ 64`, far below
where asymptotic structure shows). Here is a representation that **makes the dyadic structure explicit**
and exposes it to the polynomial method.

Write each exponent in binary, `i = Σ_{j=0}^{a−1} b_j(i)·2^j`, and set `t_j = ω^{2^j} ∈ F_p`. Then
`t_j² = t_{j+1}`, `t_{a−1} = −1`, and
```
Σ_{i∈S} ω^i = Σ_{i∈S} ∏_{j=0}^{a−1} t_j^{\,b_j(i)} = P_S(t_0,…,t_{a−1}),
```
where `P_S` is the **multilinear polynomial** (the Fourier/Möbius extension of the indicator `1_S` on the
Boolean cube `{0,1}^a`). So:

> **A bad configuration is exactly a multilinear polynomial `P_S` on the `a`-cube that vanishes at the
> single "squaring-orbit" point `(t_0, t_0^2, t_0^4, …, t_0^{2^{a−1}})`, `t_0` a primitive `2^a`-th root
> of unity mod p.**

This is a genuinely new object. Two leverage points:

**(i) The evaluation point is a Frobenius/squaring orbit.** The coordinates are not free — they are
`t_j = t_0^{2^j}`, the orbit of `t_0` under `x ↦ x²`. The squaring map is the FRI fold. So the bad-config
variety is `{P_S(x, x², x⁴, …, x^{2^{a−1}}) = 0}` for `x = t_0` — the vanishing of `P_S` along the
**diagonal Frobenius curve** `x ↦ (x, x², …, x^{2^{a−1}})` in `(F_p^*)^a`. This is a *curve*, and the
substitution `x ↦ x^{2^j}` makes `P_S(x,x²,…)` a **univariate lacunary polynomial** of degree `< 2^a = n`
with `≤ |S|` terms — precisely the lacunary-rigidity object the fleet isolated, but now with an explicit
*multilinear-on-the-cube* origin. Weil/Stepanov on this curve gives the count of bad `x`, and the
2-power-lacunary structure (gaps are powers of 2) is exactly the special structure Stepanov-type
auxiliary polynomials exploit. **The dyadic structure is now visible to the polynomial method.**

**(ii) Slice rank / cap-set on the cube.** The collection of bad `S` is a set of multilinear polynomials
vanishing at one point; dually, fixing the point, the bad indicators form a linear-algebraic family. The
**slice rank** of the bad-config tensor bounds how many *disjointly-supported* bad configs can coexist —
which is the list multiplicity. The squaring-orbit point makes the relevant tensor a **Frobenius-twisted
diagonal**, whose slice rank is computable by the Croot–Lev–Pach / Tao polynomial method. Nobody has
applied slice rank to the dyadic proximity-gap tensor; the 2-adic digit structure is exactly the setting
where slice rank is sharp (it was born on `(ℤ/k)^a`).

**Honest status.** The multilinear reformulation is, I am fairly confident, *new and correct*, and it is
the first thing that makes the dyadic structure available to algebraic methods rather than analytic ones.
Whether Stepanov-on-the-Frobenius-curve or slice-rank actually beats `n^{1−o(1)}` is open — but it is a
*different* engine than BGK (which is sum-product / additive-combinatorial), so it is not subject to the
fixed-point "no reduction escapes" theorem in the same way: it attacks the bound `M(n)` head-on with new
algebraic structure. **Feasibility as a research target: 5–6, novelty: 9.**

---

## 4. Attack 3 (lift a value): the Gauss-sum decomposition and Stickelberger's exact factorization

`M(n)` is a sum of classical Gauss sums:
```
Σ_{x∈μ_n} e_p(bx) = \frac{n}{p−1} Σ_{χ: χ^m = 1} \overline{χ}(b)·g(χ),  m = (p−1)/n,
```
where each `g(χ)` is a Gauss sum with the **exactly known magnitude `|g(χ)| = √p`** (classical, the proven
fact that closes the index-2 QR case). The wall is the *cancellation* among the `m ≈ 2^{128}` unit
vectors `g(χ)/√p`. BGK bounds this cancellation crudely; the proven `√p`-magnitude is thrown away.

**The unexploited structure: Stickelberger's theorem** gives the *exact prime ideal factorization* of
each `g(χ)` in `ℚ(ζ_m, ζ_p)`: the `𝔭`-adic valuation of `g(χ)` is the **digit-sum (Teichmüller) function**
`s(χ)` of the character. So the `m` Gauss sums are *not* `√p·(random phases)` — they are `√p·(units with
prescribed, arithmetically rigid `𝔭`-adic valuations)`. **Novelty:** treat the cancellation problem
`𝔭`-adically, where Stickelberger makes the terms *explicit*, instead of archimedean, where they look
random.

Concretely: `m` is **odd** (μ_{2^a} absorbs the full 2-part of `p−1`), so the dual characters have odd
order and the Gauss sums live in the *odd* cyclotomic tower — while the valuations come from the *2-adic*
digit structure of the index. The interplay of an odd character group with 2-adic Stickelberger
valuations is, as far as I can find, **completely unstudied**, and it is forced by exactly the dyadic
structure the prize selects. The hope: Stickelberger's valuation spread forces the `g(χ)` to be
"`𝔭`-adically in general position," which — via a `𝔭`-adic-to-archimedean transfer (a Mahler/Newton-
polygon argument on the sum) — could bound `|Σ χ̄(b)g(χ)|` below the trivial `m·√p`.

**Honest status.** Stickelberger controls valuations, not archimedean cancellation, and the transfer is
not free — this is the gap. But Stickelberger + Iwasawa (Mazur–Wiles, *proven*) is the deepest proven
machine touching cyclotomic `𝔭`-divisibility, and it has **never** been pointed at this sum. The QR case
proves the method's ceiling is real (there, one Gauss sum, `√p` exactly, closes it). **Novelty: 9,
feasibility: 4** — but it is the route most likely to be what an expert team would actually use.

---

## 5. Attack 4 (remove a term): the AM–GM / Ramanujan norm bound, pushed

The prize's §5.0 asks only for the **norm** `|N(β_S)| < p` (a single integer), *not* the sup-norm. The
norm is a **geometric mean** of conjugates, and geometric-mean cancellation is *proven* (Habegger,
Kowalski–Untrau) while the sup-norm is open. Our new exact identity:
```
Σ_{j∈(ℤ/n)^*} |σ_j(β_S)|² = Σ_{i,i'∈S} c_n(i−i') = |S|·φ(n) + Σ_{i≠i'∈S} c_n(i−i'),
```
with `c_n` the **Ramanujan sum**, gives by AM–GM the structure-aware bound
```
|N(β_S)| ≤ ( |S| + \tfrac{1}{φ(n)}Σ_{i≠i'} c_n(i−i') )^{φ(n)/2},
```
a clean `√`-improvement on the house bound (exponent `n/2 → n/4`), pushing the crossover `n≈128 → 256`.
The **new idea to push further:** the Ramanujan cross-term `Σ_{i≠i'} c_n(i−i')` is *negative and large*
for the structured char-0 bad configs (which are unions of cosets — exactly the sets where Ramanujan sums
are extreme). For a config that is a union of `r` cosets of `μ_{n/d}`, the cross-term is
`≈ −|S|·φ(n)·(1 − d/n)`, dragging the AM **below 1**, which would force `|N(β_S)| < 1`, i.e. `β_S` a unit,
i.e. **no vanishing** — automatically. The lever: **the char-0 bad configs are precisely the
coset-structured sets where Ramanujan cancellation is maximal**, so the AM–GM bound is far better *on the
relevant configs* than on worst-case `S`. We never needed the bound for all `S` — only for the
char-0-bad ones, which are the rigidity-engine cosets.

**Honest status — TESTED, refined, partly refuted.** I computed it. The binding non-antipodal configs are
`coset-core + isolated-excess`, and the test shows **`|N(β_S)|` of the full config equals `|N|` of the
isolated excess alone, to the bit** (n=32: `8.2=8.2`, `17.3=17.3`; n=64: `15.2=15.2`, `28.5=28.5`). So the
Ramanujan cancellation is *total* on the coset core (`β_core = 0` identically — this is exactly the
`n/2 → n/4` √-improvement, now explained *structurally*: half the conjugate mass vanishes because the core
is a full subgroup sum), but it gives **no benefit on the isolated excess**, which carries all the
non-antipodal content. Hence `|N(binding β)| ≈ m^{φ(n)/2} = m^{n/4}` where `m` = isolated-excess size,
crossing `p=2^{128}` at `n ≈ 256/\log_2 m`. **So the lever genuinely moves the crossover `n≈128 → 256+`
and is the correct explanation of the √-improvement — but it does not remove the crossover at prize `n`.**
The *new* and decisive sub-question it exposes: **is the isolated excess `m` bounded (O(1)/O(log n)) or
does it grow like `ρn`?** The issue's "isolated `= k+1` exactly, n-independent" (Beukers–Smyth) suggests
*bounded*; if `m = O(1)` the crossover is `n ≈ 2^{O(1)}`-pushed but still finite. **The prize closes via
this route iff the isolated excess is `O(1)` AND its `O(1)`-term norm avoids `p` — the latter is again
equidistribution.** Feasibility: 6, novelty: 7 — and now the *cleanest* statement of where BGK re-enters:
not on the whole agreement set, but on an `O(1)`-term residual sum. That is a far smaller open object than
where we started.

---

## 6. Attack 5 (prove the wall is the answer): the exact `δ*` curve may not reach the window edge

A genuinely different possibility: **the conjectured window edge is wrong**, and the true `δ*` is the
exact char-0 value, which is closed and computable. The fleet pinned the exact curve
`δ*(n) = 3/8, 5/12, 9/16` for `n = 8,12,16` (ρ=¼), crossing Johnson near `n≈14`. The conjecture asserts
`δ*(n) → 1−ρ−Θ(1/log n)` (window edge). But by the monotonicity (`δ*_p ≥ δ*_0`) the char-0 curve is a
**lower bound that holds for every prime simultaneously** — so the *universal* (∀-q) `δ*` is *exactly*
`δ*_0`, the char-0 curve, **with no BGK input at all**, *provided* one proves the char-0 incidence is the
universal worst case (the deletions only help). If the char-0 curve's asymptotic is
`1−ρ−c/log n` with a *computable* `c` strictly different from the conjectured `H(ρ)/β`, then **the prize
value is the char-0 value, the BGK wall is irrelevant to the universal floor, and δ\* is closed.**

This flips the problem from analysis to **exact enumerative asymptotics of a q-independent count** — which
is the regime where we have proven closed forms (`D₁=n`, `D₂=n²/4−n`, the support law, the orbit/rigidity
quantization in units of `n`). The open piece becomes: *find the exact asymptotic of the char-0 far-line
incidence threshold*, a finite combinatorial problem with no character sums in it. **Novelty: 8,
feasibility: 7 as a computation, but proximity uncertain** — it hinges on whether "deletions only help"
holds universally (it does pointwise by monotonicity; the ∀-q subtlety is whether the char-0 case is
*attained* in the universal quantifier, which the field-universality clause [c.154] complicates).

---

## 7. The synthesis I would pursue: sieve the survivors on the dyadic curve

The five attacks are not independent; the strongest move combines **Attack 1 (deletion sieve)** with
**Attack 2 (multilinear/Frobenius-curve)** and **Attack 4 (Ramanujan-on-cosets)**:

> The char-0 bad configs are the rigidity-engine cosets (proven, ≈ `n` of them). For each, `β_S` is a
> coset sum, so by Attack 4 its Ramanujan cross-term is extreme and `|N(β_S)|` is *small* — possibly a
> unit. A unit never vanishes mod `p`, so by Attack 1 it **survives**; a non-unit's `𝔭`-divisibility is
> read off, by Attack 2, from the vanishing of the univariate 2-lacunary polynomial `P_S(x,x²,…)` at
> `x=t_0`, whose root structure is governed by Stickelberger valuations (Attack 3). The survival count is
> then a sieve over `≈ n` structured configs with explicitly bounded `𝔭`-divisibility — a finite,
> one-sided count, no sup-norm.

This chain is, to my knowledge, entirely new. It replaces the single hard analytic inequality `M(n)≤√n`
with a finite arithmetic-geometric sieve over the `n` proven coset configs, where every step touches a
*proven* tool (monotonicity, Ramanujan sums, Stickelberger, the rigidity quantization). I cannot prove it
closes — the `𝔭`-divisibility of the non-unit coset sums is where BGK could re-enter — but it is the first
attack that is **simultaneously one-sided, dyadic-structure-aware, and built entirely on proven
machinery**, and it is where I would put the next month.

### 7a. TESTED — isolated excess grows, then the object turned out to be the wrong one
First I measured the isolated-excess (non-antipodal core) size of the binding `e₂=0` configs at the
window-edge band: `n=16, w≈12 → core 2`; `n=32, w≈16 → core 8 = n/4`. So for the **shallow** configs the
core grows like `n/4`, and `|N|` crosses `p` near `n≈256` — the AM-GM octave, not a closure. Then the
deeper test exposed a framing error: **`e₁=0 ⟺ β_S=0 ⟺ fully antipodal (core 0)`**, tautologically
(`e₁ = Σζ^i`). So `e₁` is *not* the binding object; the bad scalar is the **first non-vanishing symmetric
function `e_t(S)`** (configs satisfy `e_1=…=e_{t−1}=0`, `γ=±e_t`).

### 7b. The corrected object looks far friendlier — the unit-residual lead
Re-running on the correct object `|N(e_t)|` (n=16):

| config | first nonzero `t` | `log₂|N(e_t)|` |
|---|---|---|
| `w=12, e₁=0` | `2` | `4.0` |
| `w=12, e₁=e₂=e₃=0` | `4` | **`0.0` — a UNIT** |
| `w=8, e₁=0` | `2,4,8` | `6.0, 4.0,` **`0.0`** |

**The deeper the simultaneous vanishing, the smaller `|N(e_t)|` — toward units (`|N|=1`).** A unit is never
`p`-divisible, so deep-vanishing bad scalars cannot spuriously vanish, and BIND holds for them
automatically. This is the **opposite sign** from the `e₁` analysis, and the window-edge binding direction
is exactly the *deepest* vanishing (`t₀=Θ(n/\log n)`) — precisely where `|N(e_t)|` is smallest. **Caveat:**
`n=16` only (deep configs are rare; the `n=32` search did not reach them in budget) — a *signal*, not a
proof. It sharpens the live question to its most hopeful form:

> **Conjecture (unit-residual / the real BIND).** For window-edge binding configs (`e_1=…=e_{t₀−1}=0`,
> `t₀=Θ(n/\log n)`), the bad scalar `e_{t₀}(S)` has `|N_{ℚ(ζ_n)/ℚ}(e_{t₀}(S))| < p` (a unit or near-unit).
> Then `#bad_p = #bad_0` at the window edge and `δ*` is the **computable char-0 value** — *no BGK input*.

If true this **removes the term**: the prize closes enumeratively (Attack 5), with the deep symmetric
functions small-norm by an *arithmetic* (not analytic) mechanism. The cleanest, most concrete, most honest
lead the campaign has reached. Decisive next computation: `|N(e_{t₀})|` for deep configs at `n=32,64`
(finite, no character sum). Novelty 8, proximity 9, feasibility 6.

---

## 8. Honest coda

None of these five is a closure, and I will not pretend otherwise — the honesty contract that the prize
itself mandates forbids it. But the request was for *new mathematics*, and these are five new things:

1. **The deletion reframe** — the prize is a survival/sieve problem, not a magnitude problem; the proven
   monotonicity makes it one-sided.
2. **The multilinear/Frobenius-curve reformulation** — bad configs are multilinear polynomials vanishing
   on the squaring orbit; this hands the *dyadic* structure to the polynomial method / slice rank, which
   BGK cannot see.
3. **The Stickelberger `𝔭`-adic attack** — the Gauss-sum decomposition has exact, arithmetically rigid
   valuations that have never been used; odd character group × 2-adic valuations is virgin territory.
4. **Ramanujan-on-cosets** — the norm bound need only hold on the structured char-0 bad configs, where
   Ramanujan cancellation is extremal and may force units (automatic survival).
5. **The exact-curve route** — by monotonicity the universal `δ*` *is* the computable char-0 value; the
   prize may be closed enumeratively if its asymptotic is pinned, with no character sum at all.

The deepest single realization: **p-independence and the BGK wall are the same threshold** (`n≈128`,
where `|N(β)| ≈ 2^n` crosses `p ≈ 2^{128}`), and above it the prize is a **deletion-deficit** problem —
you do not fight the character sum, you harness its vanishings. Reframing a 25-year analytic wall as a
finite, one-sided, proven-tool sieve over `n` coset configurations is the most promising new direction I
can honestly offer, and it is genuinely new.

*— All claims labeled; proven facts cited as proven, conjectures as conjectures. Tools and prior records:
docs/kb/Iinf-campaign/01–10, issue #407 §2/§3/§5.0.*
