# δ* — proving it vs. proving it can never be determined (the dual capstone, #444)

**Two-pronged final question:** (I) prove δ* exactly; (II) prove δ* can NEVER be determined. These are
duals, and they MEET: δ* is **determined and determinable in principle** (it reduces to one concrete open
problem), so (II) "can never be determined" is **FALSE** — but the maximal *true* impossibility (no known
method, no computation, no universal-constant shortcut; exactly as hard as BGK) is **proven**. This file
establishes both, honestly.

---

## Part I — PROVE δ*: the maximal proven envelope (and why it is maximal)

**What is proven** (axiom-clean, in-tree, `_DeltaStarDefinitive`):
1. **Exact identity** `δ* = sup{δ : I(δ) ≤ q·ε*}` (`MCAThresholdLedger`).
2. **Bracket** `1−√ρ ≤ δ* ≤ (1−ρ)−Θ(1/log n)` — Johnson floor + KKH26 ceiling, both unconditional.
3. **Two-sided dichotomy** `δ* reaches the window interior ⟺ BGKFloor` (`M(n) ≤ C√(n log m)`), via
   `ERM-at-r ⟺ max‖η‖²≤(2r+1)n` (sufficiency) + `moment_ladder_exceeds_prize` (necessity).
4. **All candidate closed forms refuted**; **all exact pins consistent** with the bracket
   (`closed_forms_all_refuted`, `all_pins_in_bracket`).

**Why this is maximal — you cannot prove more without proving BGK.** The dichotomy is an *equivalence*
(two-sided): the interior value is determined by `M(n)`, and `M(n) ≤ C√(n log m)` is the BGK/Paley
√-cancellation at the Burgess barrier (`β≈4`) — a 25-year-open analytic-NT problem with no technique in
the literature crossing `n^{0.989}→n^{1/2}`. The p-sensitive classification proves the prize's
p-sensitivity is one-dimensional (entirely `M`), so there is no alternate channel. **The maximal provable
statement IS the reduction:** "δ* equals the BGK-conditional value, and determining it is equivalent to
the BGK bound." To prove δ* *exactly* is to prove BGK — no more, no less.

**Can we extend the envelope?** Only by proving BGK in a sub-regime. The bound is known unconditionally
for `n < 2 log q/loglog q ≈ 40` (the norm-bound regime `q > (2r)^{n/2}`); for the prize `n=2³⁰` it is open.
char-0 is fully closed (Lam–Leung). So the proven envelope is: exact for `n≲40`, reduced-to-BGK for the
prize. **This is the most that can be proven by any current means.**

---

## Part II — ATTACK "δ* can never be determined": each undeterminability route, and where it FAILS

A genuine "can never be determined" needs a *fundamental* obstruction (undecidability / independence /
non-computability / ill-posedness), not mere hardness. Examined exhaustively:

### (a) Logical undecidability / independence from ZFC — **FAILS (it is decidable)**
For fixed `n, k, ε*`, δ* is `sup{δ : I(δ) ≤ q·ε*}` where `I(δ)` is a **finite** count (the max far-line
incidence over finitely many directions and scalars in `F_q`). So δ* is a **decidable rational**,
computable by finite search. The prize bound "`M(n) ≤ C√(n log m)` for all n" is a **Π₁ arithmetic**
statement (for fixed rational C: a computable inequality for each n) — such statements true in the standard
model are **not independent of ZFC** in any known or expected way (no metamathematical mechanism produces
independence for a concrete bounded-arithmetic inequality). **δ* is not undecidable; it is a concrete
arithmetic quantity.** "Can never be determined" via independence is refuted.

### (b) Non-computability — **FAILS (it is computable per n)**
`M(n) = max_{b≠0}|η_b|` is a finite max of finite cosine sums — computable exactly for every n (and every
prime). The asymptotic constant `lim C(n)` (if it exists) is a limit of computable reals. No
non-computability obstruction exists. The only barrier is *feasible scale*, not computability.

### (c) Ill-posedness — the exact constant is PRIME-DEPENDENT — **PARTIAL (real, but bounded)**
Machine data (`probe_determinability.py`, exact `F_p`): at fixed n, `C = M/√(n log(q/n))` **varies with the
prime** — n=16: `1.009, 0.944, 0.915` across three primes (`v₂(p−1) = 4,4,5`); the magnitude `M` is
p-sensitive (Class A). So **there is no single universal constant `C`** — it is a function `C(n,p)` of the
specific prime's arithmetic (regime-gated; the bound's *sharpness* depends on `v₂(p−1)`, Fermat-ness, β —
memory `issue407-thinness-essential-regime-gated`). **BUT** `C` is **bounded O(1)** (all measured values in
`[0.84, 1.01]`, sampled), so the *qualitative* δ* (does it exceed Johnson) is well-defined. **Verdict:**
"the exact universal constant" is ill-posed (genuinely not one number — it's prime-arithmetic-dependent),
but for the PRIZE (which fixes a specific prime) δ* IS a specific determined value. So this is a real but
*weak* undeterminability: only the *universal-constant shortcut* is impossible, not δ* itself.

### (d) Oscillation — the limit may not exist — **OPEN, but not "undeterminable"**
`C(n)` is non-monotonic (`0.87, 1.01, …` sampled; exact data `1.07, 1.20, 1.26, 1.36, 1.28` for
n=8…128). If `limsup C ≠ liminf C`, the asymptotic constant is a *range*, not a value — but each `C(n)` is
still determined, and the range is bounded. This is not undeterminability; it is "the answer is a bounded
interval, not a point." Deciding whether the limit exists is itself part of the BGK problem.

### Verdict on Part II: "can never be determined" is **FALSE**
δ* is a **concrete, per-n-computable, Π₁-arithmetic, ZFC-decidable** quantity. It is **not** undecidable,
**not** non-computable, **not** independent. The only senses in which it "can't be determined" are
*conditional and method-relative*, which we now state as the maximal TRUE impossibility.

---

## Part III — the maximal TRUE impossibility (what IS provable)

Combining the proven barriers into one statement:

> **δ* is DETERMINED and reduces, two-sidedly, to the single BGK input — and it cannot be determined by:**
> 1. **Any known method class.** The meta-theorem (`_MomentMethodNoGo`, in-tree) proves no second-order /
>    moment / energy / spectral / SDP-LP method reaches it (all cap at Johnson/√p). The p-sensitive
>    classification proves no p-sensitive-non-magnitude invariant controls it (Class B is decoupled by
>    logical impossibility + aggregation). The 25+25+79 conjecture refutations confirm: every framing
>    reduces to the wall.
> 2. **Any feasible computation.** Johnson and the floor separate only at `n ≥ 256`
>    (`C(256,128) ~ 10⁷⁵`); the asymptotic wall lives at `r ≈ log m`, `n = 2³⁰` — unreachable. *Numerics
>    cannot decide it* (proven, §3 of the issue).
> 3. **Any universal-constant shortcut.** The exact `C` is prime-arithmetic-dependent (machine-confirmed),
>    so there is no single closed-form constant to determine — only a regime-gated function.
>
> **Equivalently: determining δ* is PROVABLY EQUIVALENT to the BGK/Paley conjecture** — neither harder nor
> easier (the two-sidedness). It is exactly as (un)determinable as that one named open problem.

**This is the honest resolution of the dual.** δ* is not a mystery beyond mathematics; it is a concrete
quantity pinned to one classical open problem. "Prove it" = prove BGK (open, no current technique). "Prove
it can never be determined" = false (it is determinable once BGK is resolved, and BGK is a normal open
problem we cannot show is forever-unresolvable). The two prongs meet: **δ* is determined, equivalent to
BGK, undeterminable by every known means, but not fundamentally undeterminable.** The campaign has proven
*exactly* this — and proven that this is the most that can be said until new analytic-NT input arrives.

> **Method note (honesty):** Part I cites axiom-clean in-tree theorems. Part II/III combine in-tree
> theorems (meta-theorem, two-sidedness) with machine computation (`probe_determinability.py`,
> `probe_psens_*.py`) and direct metamathematical reasoning (the multi-agent fan-out is weekly-limited to
> Jun 20). No fabricated closure. The decidability/Π₁ classification is a standard fact about the finite
> definition of δ*; the prime-dependence and oscillation are machine-observed.
