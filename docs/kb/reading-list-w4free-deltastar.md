# W4-free δ* — reading list & honest resolution (#407)

Five recent papers most relevant to a **W4-free** pin of δ* (avoiding the worst-case incomplete
character sum `max_b|Σ_{x∈μ_n} e_p(bx)| ~ √(n log(q/n))`, the BGK/Bourgain 25-year-open wall).
Compiled by a multi-agent research workflow (13 agents, 2026-06-13).

1. **Crites & Stewart, "On Reed–Solomon Proximity Gaps Conjectures" (2025)** — eprint 2025/2046,
   STOC 2026. Proves the up-to-capacity (1−R) conjecture FALSE in all three forms (correlated
   agreement, WHIR mutual-CA, deep-FRI list-decodability); modifies the pin to
   δ* = 1 − H_q(δ) − 1/n − η — structurally identical to the in-tree δ* = 1−ρ−H(ρ)/(β log₂ n);
   gives the CA-error↔list bridge L = O(εq) matching the budget q·ε* ≈ n.

2. **Goyal & Guruswami, "Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed–Solomon
   Codes" (2025)** — ECCC TR25-166 / eprint 2025/2054. THE live W4-free mechanism: reaches 1−R−η at
   LINEAR field size O_η(n) via a curve-pruning local property ("curve/V-decodability") that
   EXPLICITLY avoids character sums — but only for RANDOM evaluation points; transfer to fixed
   dyadic μ_n is the open prize gap. (Supersedes withdrawn arXiv 2601.10047.)

3. **Ben-Sasson, Carmon, Habock, Kopparty & Saraf [BCHKS25], "On Proximity Gaps for Reed–Solomon
   Codes" (2025)** — ECCC TR25-169 / math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf. A genuine
   second-moment/variance concentration argument on subspace-polynomial roots that reaches ONLY
   Johnson (1−√ρ) — demonstrating pure concentration on this object recovers exactly the √n deficit.

4. **Brakensiek, Gopi & Makam, "Generic Reed–Solomon Codes Achieve List-Decoding Capacity" (2022/23)**
   — arXiv:2206.05256 (+ Brakensiek–Dhar–Gopi, "Improved Field Size Bounds for Higher-Order MDS
   Codes," ISIT 2023, arXiv:2212.11262). The algebraic route: higher-order MDS(ℓ) ⟺ generalized-
   Singleton list bound via GM-MDS zero-patterns (no character sums); BUT the field-size lower bound
   q ≥ C(n−2,k−1) ≈ 2^{nH(ρ)} provably EXCLUDES the prize regime q = n^β.

5. **Alrabiah, Guo, Guruswami, Li & Zhang, "Random Reed–Solomon Codes Achieve List-Decoding Capacity
   with Linear-Sized Alphabets"** — arXiv:2304.09445 (Advances in Combinatorics). Capacity list-size
   for random RS at linear field size via probabilistic zero-pattern analysis — the object that must
   be derandomized to the explicit dyadic domain.

Companion survey: **Arnon–Boneh–Fenzi, "Open Problems in List Decoding and Correlated Agreement"**
(eprint 2026/680).

## Honest resolution (W4-free question)
- The imprimitive 2-power-tower monomial lines fold SELF-SIMILARLY W4-free (even/odd code split,
  geometric telescope to ~n/2 < budget). But every fold bottoms out on a PRIMITIVE base line, and
  primitive-line incidence = RS[k+1] list size on a full subgroup = non-principal eigenvalue of
  Cay(F_q,μ_m) = **W4** (Paley-graph object). The "primitive lines concentrate" premise IS the
  unproven square-root cancellation.
- The ALGEBRAIC higher-order-MDS route provably CANNOT pin at prize field size (needs q ≥ 2^{nH(ρ)};
  μ_n fails MDS(3) via antipodal sum-zero pairs — `HigherOrderMDSOrderThreeFail`).
- The LIVE combinatorial W4-free route (fleet, `FactorizationRigidity.lean`): δ* = the q-independent
  COSET-SUMSET count at the extremal monomial direction (Kambiré edge δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*),
  UPPER bracket proven). Lower-bracket optimality reduces to 4 combinatorial pieces; (2) coset-
  saturation ("beyond Johnson, every large agreement set is a μ_d-coset") and (4) Kambiré sumset-max
  (#bad = |H^{(+r)}| = distinct r-subset-sums of μ_s) are W4-free, verified-not-proven.
- **Verdict: no closed W4-free pin in the prize window interior yet.** The escape exists in the
  literature (GG25) only for random points; the irreducible open step is the transfer to fixed μ_n.
