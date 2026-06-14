# δ* #407 literature sweep — char-p transfer wall precisely cited (2026-06-14)

Focused sweep for the SPECIFIC reduced forms the prize now sits on (char-p vanishing sums;
trinomial / shifted-subgroup exponential sums; explicit BGK). Five papers found; the headline
is that **Lam–Leung (1996) is the exact citation for the char-p transfer step**, and it pins
why the wall is a wall.

## The headline: Lam–Leung char-p structure = the e_i wall, precisely

**[LL96fin] Lam–Leung, "Vanishing Sums of m-th Roots of Unity in Finite Fields"** (math/9605216;
J. Algebra). Main structural fact: the weight set
  W_p(m) ⊇ ℕp + ℕp₁ + … + ℕp_r   (p_i = prime divisors of m).
For dyadic m = 2^μ the only prime divisor is 2, so **W_p(2^μ) ⊇ ℕp + 2ℕ**. Consequence (the
piece we need): a vanishing sum of 2^μ-th roots of unity in char p of weight t
  • either decomposes into char-0 **negation pairs** (weight ∈ 2ℕ, the char-0 Lam–Leung law), OR
  • is a genuinely-new char-p relation, which requires the ℕp part ⟹ **weight ≥ p**.
Equivalently (Teichmüller lift + norm): a new relation of weight t forces p ∣ N(Σζ_i) ≠ 0, so
**p ≤ N(Σζ)^{1/·} with norm exponent φ(m) = φ(2^μ) = n/2.** This IS the Galois-prime mechanism
p^r∣N(α) I derived this session — now with a 1996 citation. It pins the wall EXACTLY:

  char-p transfer of the energy bound E_r(μ_s) ≤ (2r−1)‼·s^r is CLEAN ⟺ q > t^{φ(s)}, t ~ ln q,
  where s = the subgroup the worst bad-config lives in.
   • full group s = n: φ(n) = n/2 ⟹ need q > t^{n/2} — HOLDS only for n < 2 log q/log log q ≈ 40;
     FAILS at the prize n = 2^30 (the known wall).
   • small s*: φ(s*) small ⟹ q = n^β > t^{φ(s*)} HOLDS ⟹ clean. **This is the only escape**, and it
     is exactly the small-subgroup synthesis. ⟹ the entire prize hinges on the growth of s*(n)
     (this session's probes: s*=8 at n≤16, q-independent; n≥32 computationally walled).

## Candidate routes (q-uniform, might dodge the norm-exponent wall)

**[MSS18] Macourt–Shkredov–Shparlinski, "Multiplicative Energy of Shifted Subgroups and Bounds on
Exponential Sums with Trinomials in Finite Fields"** (Canad. J. Math. 70(6), 2018). Bounds
exponential sums with **trinomials** via a new collinear-triples/multiplicative-energy bound for
**shifted** multiplicative subgroups. The far-line incidence object is x^a+γx^b on μ_n — a
trinomial/shifted-subgroup energy. CANDIDATE: a direct trinomial-energy incidence bound that is
uniform in q (energy method, not norm), potentially sidestepping the φ(n)=n/2 exponent. TO READ:
does its energy exponent give B ≤ √(n log q) for n ≪ √q? (likely below its threshold, but check.)

**[Bur-GAP25] "Burgess-type character sum estimates over generalized arithmetic progressions of
rank 2"** (arXiv 2509.07765, Sept 2025). The frequency set {0,…,k−1, a, b} of the sparse-cyclic-
code lens IS a **rank-2 GAP** (a length-k block + 2 generators). CANDIDATE: a Burgess bound over
rank-2 GAPs might bound I(δ) directly. CAVEAT: Burgess gives cancellation only above ~p^{1/4};
μ_n with n ≪ √q is below threshold — likely does not close, but the rank-2-GAP framing is novel.

## Confirming the wall is open

**[BG-small24] "Exponential sums over small subgroups, revisited"** (arXiv 2401.04756, 2024) and
**[2003.06165] "New estimates for exponential sums over multiplicative subgroups and intervals"**:
best explicit BGK-type exponents; in the limiting H ~ p^{1/4} regime, Bourgain–Garaev give
H^{1−175/9437184+o(1)} — a microscopic power saving, polynomially short of the √(n log q) target.
**[Shp-open] Shparlinski, "Open Problems on Exponential and Character Sums"**: lists making BGK
EXPLICIT (all constants) as an OPEN problem. ⟹ confirms: no q-uniform proven bound reaches the
prize target for n ≪ √q. The wall (BCHKS 1.12 / Paley graph) stands.

## Net
The sweep did NOT find a closure (the wall is confirmed open in the 2024–2025 literature). It DID
(a) give the char-p transfer step a precise citation [LL96fin] and pin the wall to the norm exponent
φ(n)=n/2, (b) confirm the small-s reduction is the unique escape ⟹ s*(n)-growth is the prize, and
(c) surface two genuinely-new candidate routes ([MSS18] trinomial-energy, [Bur-GAP25] rank-2-GAP
Burgess) worth a focused read for a q-uniform bound. NOT a closure.
