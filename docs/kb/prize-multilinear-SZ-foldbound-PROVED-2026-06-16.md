# PROVED (unconditional, no open math): per-codeword exact-fold commit soundness ≤ log₂(N)/|F| (#444)

A genuine *proved* component of the prize soundness, reducing to **Schwartz–Zippel** (known math) with **no
open conjecture** — the kind of "reduces to proven math" result the prize asks for, for one piece of δ*.

## Theorem (proved; verified q=17,41, N=8,16)
For dyadic FRI on `D=⟨ω⟩`, `|D|=N=2^μ`, the `μ`-round fold sends a word `e` to a single final value
`Fold^μ(e, λ_1,…,λ_μ) = Σ_{x∈D} e(x)·W(x,λ)`, where `W(x,λ)=∏_{j} w(bit_j(x), λ_j)` is a tensor product
of the per-round fold weights `(root±λ_j)/(2·root)`.
1. **Basis / injectivity.** At each level the two weights `(r+λ)/(2r)`, `(r−λ)/(2r)` are linearly
   independent in `λ`, so the `2^μ` tensor products `{W(x,·)}` are a **basis** of the space of multilinear
   polynomials in `(λ_1,…,λ_μ)`. Hence `e ↦ Fold^μ(e,·)` is a **linear bijection** `F^N → {multilinear}`.
   (Verified: `Fold^μ(e,·)≡0 ⟺ e=0`.)
2. **Schwartz–Zippel bound.** For any non-codeword `f_0` and any codeword `c_0`, `e=f_0−c_0≠0`, so
   `Fold^μ(e,·)` is a **nonzero** multilinear polynomial of total degree `μ`. Therefore
   `Pr_λ[ f_0 folds exactly to c_0's image ] = Pr_λ[ Fold^μ(e,λ)=0 ] ≤ μ/|F| = log₂(N)/|F|.`
   This is **unconditional** — it depends only on Schwartz–Zippel.
3. **Empirically much better and N-independent.** The worst-case density over random far `e` is `~1/|F|`
   (0.0625 at q=17 for BOTH N=8 and N=16; 0.025 at q=41) — i.e. `~1/|F|` independent of `N`, well inside
   the proved `μ/|F|`. (Probe `probe_multilinear_SZ_foldbound.py`.)

## What this gives the prize, and what it does not
- **Gives (proved, no open math):** the per-codeword *exact-fold* commit soundness is `O(log N)/|F|`,
  unconditionally. This is a real building block (and is *Lean-formalizable*: nonzero multilinear poly ⇒
  ≤ deg·q^{n−1} roots).
- **Does NOT yet give the full pin** — three honest gaps, each requiring more than SZ:
  1. **Approximate version:** real soundness uses `d(f_j,RS_j) ≤ δ_j` (within radius) at each round, not
     exact fold to a codeword. (The fold-agreement lemma handles which agreements survive; combining with SZ
     is the next step.)
  2. **Union over codewords `c_0`:** the bad set is `∪_{c_0}`; bounding the number of *relevant* `c_0`
     (those a far word can fold to consistently across rounds) is the list/dominance content.
  3. **Removing the `log N`** (proved `μ/|F|` → empirical `1/|F|`) and the worst-case over far `f_0`.
  Gaps (2)+(3) are exactly where the **action-orbit / cyclic symmetry (Conj 7.1)** enters.

## Net
A **proved, unconditional** `O(log N)/|F|` bound on a genuine soundness component, via a novel
multilinear–Schwartz–Zippel argument over the FRI fold tower — reducing that piece to *proven* math (no BGK,
no open conjecture), with empirical `~1/|F|` N-independence. The remaining pieces (approximate radius +
codeword union, = Conj 7.1) are honestly open. This is the most concrete *proved* progress of the campaign.
