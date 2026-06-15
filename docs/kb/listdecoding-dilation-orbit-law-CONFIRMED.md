# The explicit-smooth-RS list size in the window is CONSTANT (dilation orbit) — independently confirmed (#444)

The RS-list-decoding army's "Dilation-Orbit List Law" (ranked N8/I8), **independently confirmed by a separate
exact list-size computation** (`scripts/rust-pg/src/bin/listsize.rs`, C(n,k)-interpolation enumeration, NOT a
char-sum proxy). This is the first direct measurement of the literal list size of explicit smooth RS in-regime.

## The measured structure (exact, p-independent across 2+ primes)

Worst-case list `L(u,δ) = #{deg<k codewords agreeing with u on ≥(1−δ)n points}`, extremal word `u = x^{n/2^j}`
(imprimitive 2-power monomial):

| regime | DEEP window (t ≥ ρn + Θ) | NEAR capacity (t = k+1, k+2) |
|---|---|---|
| n=16,k=4 (ρ=1/4) | **L=2** | 12 (t=k+1) |
| n=24,k=6 (ρ=1/4) | **L=2** (t=9..12) | 35, 219 (t=8,7) |
| n=16,k=2 (ρ=1/8) | **L=2** (whole window) | 7 (t=k+1) |

- **Deep in the window: `L = 2` (CONSTANT)** — not poly-growing.
- **Near capacity (t=k+1,k+2 = ρn+O(1)): `L` spikes ~n²** (the Singleton count of k-subsets sharing k+1 points).
- `x^k`, `x^{n−1}` give L=0 (not binding); the binding word is the **2-torsion monomial `x^{n/2}`** (matches the
  covering-radius mechanism — the order-2 character is what makes the smooth domain special, absent for prime n).

## The mechanism (the LOWER bound is PROVEN)

The **dilation group μ_n acts on the codeword list**: `f(x) → f(gx)` preserves deg<k and permutes the list of any
μ_n-dilation-invariant word. So the worst-case list ⊇ ONE ORBIT of the stabilizer of the extremal word, of order
`O(1) = 2^{v_2(...)}`. **L ≥ orbit = O(1) is proven by the group action.** The transient near-capacity spike
(~n²/2 at t=k+1) is the Singleton-bound C(t,k)-count, structurally separate.

## The reduction (where the floor actually sits)

The constant-list law gives a clean **list-decoding statement of the floor**:
> **Floor ⟺ no codeword outside the dilation orbit** for any received word, at radii in the window interior.

- **LOWER bound `L ≥ orbit = O(1)`: PROVEN** (group action).
- **UPPER bound `L ≤ orbit` (no extra codewords): = the open core** = the Hab25 exception-set bound past Johnson
  (`|E| ≤ 2^{v_2(n)}` per pencil) = reduces to the far-line incidence / BGK char-sum wall.

## The honest scale caveat (same as c.348)

The "deep window L=2 vs near-cap spike ~n²" transition location is exactly the floor edge `ρn + Θ(n/log n)` —
and at feasible n (≤32), `ρn+Θ(n/log n) ≈ k+2`, so the spike sits at the blurry window/capacity boundary. Whether
the spike (n²) is INSIDE or OUTSIDE the window interior depends on the Θ(1/log n) constant — the same open
question. So: **L=O(1) is confirmed where the window is unambiguously interior; the constant-vs-spike transition
IS the floor location**, reducing (again) to the BGK wall — but now as a clean list-decoding statement.

## Net

Genuine forward progress: the literal worst-case list of explicit smooth RS in the window is a **constant
(dilation orbit, =2)**, measured exactly and p-independently, with poly growth quarantined to the capacity
boundary. The orbit lower bound is PROVEN; the floor reduces to "no codeword outside the orbit" = the BGK wall,
restated in clean list-decoding terms. Also: BKR superpoly-list needs a subfield → impossible over prime F_p, so
the only known superpoly route is closed in-regime (consistent with the constant lists). NOT a closure; the
sharpest list-decoding form of the floor yet. Tool: `scripts/rust-pg/src/bin/listsize.rs`.
