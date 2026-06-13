
## Theme A (cont.) — the perfect-B_r rigidity of prime roots of unity

Probe: `scripts/probes/probe_conj_perfect_Br.py`. Verified p=3,5,7,11; r=2..6 (incl. r≥p).

- **A5 (perfect-B_r theorem — PROVED, strong survivor).** For every odd prime `p` and EVERY `r≥1`,
  `μ_p ⊂ ℂ` is a perfect `B_r` set: the only solutions to `a_1+…+a_r = b_1+…+b_r` (`a_i,b_i∈μ_p`)
  are permutations. Equivalently `E_r(μ_p) = Σ_{size-r multisets M}(orderings M)²` (the pure
  permutation count), a closed polynomial in `p`.
  **Proof (rigorous):** the lattice `{c∈ℤ^p : Σc_iζⁱ=0}` equals `ℤ·(1,…,1)` (Φ_p is the minimal
  polynomial of ζ, so the unique relation is the p-sum). An `E_r` relation has `c_i=mult_a(i)−mult_b(i)`
  ⟹ `c=m(1,…,1)`; `Σc_i = r−r = 0 = mp ⟹ m=0 ⟹` a,b the same multiset. ∎
  **Refutation checks passed:** (i) r<p AND r≥p both match (so it's "all r", not just r<p — my initial
  r<p hypothesis was itself too weak); (ii) `E_r(μ_p)` differs from a random Sidon set's at r=3
  (1645 vs 1663) — so this rigidity is SPECIAL to prime roots of unity, not generic to Sidon sets.
  **Significance:** prime-order roots of unity are simultaneously Sidon in ALL orders — maximal
  additive rigidity. Contrasts with composite `n` (relations from Φ_d, d|n) and 2-power `n` (antipodal
  B_2 failure, A1). This is the additive-rigidity root cause of why the prize's 2-power (NTT) domain is
  the hard case and odd-prime domains are generic. Count promoted: +1 (now 5 total).

## Theme B — exact higher-energy closed forms for the 2-power (NTT) subgroup

Probes: `scripts/probes/probe_conj_2power_energy.py`, `probe_conj_e4_2power.py`. Verified n=4..64.

- **B3 (2-power Gaussian-energy closed forms — SURVIVOR, leading term PROVED).** For `n=2^k`:
    `E_2(μ_n) = 3n²−3n`
    `E_3(μ_n) = 15n³−45n²+40n`
    `E_4(μ_n) = 105n⁴−630n³+1435n²−1155n`
  Leading coefficient is `(2r−1)!!` (the GAUSSIAN moment): 3, 15, 105 for r=2,3,4. PROVED in leading
  order by the Bessel reduction (`E_r^∞(μ_{2^μ}) ≤ (2r−1)!!nʳ`, wakesync `RungBesselEnergy.lean`);
  the exact lower-order polynomials are NEW closed forms (verified, not previously pinned).
  **The A5↔B3 dichotomy (the additive-rigidity spectrum):**
    odd prime `μ_p`: `E_r ~ r!·nʳ`        (MINIMAL — perfect B_r, permutation-only)
    2-power `μ_{2^k}`: `E_r ~ (2r−1)!!·nʳ` (MAXIMAL-Bessel — antipodal-inflated, Gaussian)
  Since `(2r−1)!! ≥ r!` with equality only at r=1, the 2-power subgroup carries strictly more higher
  energy at every order r≥2 — the quantitative root cause of why the prize's NTT (2-power) domain is
  the additively hardest case and odd-prime domains are generic. Count promoted: +1 (now 6 total).
