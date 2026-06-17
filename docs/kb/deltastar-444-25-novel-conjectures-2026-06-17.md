# 25 Novel NT Conjectures to Pin δ* Exactly — generation + adversarial refutation (#444)

**Purpose.** Per the directive to generate 25 *highly novel* NT hypotheses to prove δ* exactly, rated on
**feasibility / novelty / notBGK** (likelihood NOT to reduce to the BGK wall), then attack/refute all.

**Method.** A loop-until-target multi-agent generation (16 distinct mathematical angles, dead-ledger
re-skins BANNED, independent skeptical judges gating on novelty≥9) produced **107 distinct candidate
conjectures**; the 25 below are the curated highest-notBGK, mechanism-diverse survivors. Each was then
attacked by **3 adversarial lenses** (reduce-to-BGK / reduce-to-Johnson / machine-countermodel).

**⚠️ The honest prior.** The campaign has run 79/50/100/140-conjecture sweeps with **0 survivors** —
essentially everything reduces to the char-p BGK/Paley √-cancellation wall `M(n)≤C√(n log m)`. The
`notBGK` axis is the whole difficulty: even genuinely-novel *mechanisms* (Maslov index, QUE rate,
monodromy drop) tend to re-enter the wall when you trace where the actual estimate lives. The value of
this exercise is (i) the *most orthogonal* framings found, and (ii) the *precise reduction* showing how
each re-enters the wall — which sharpens exactly what an escape would need.

> **Scores are self/judge-assessed at generation time; the adversarial VERDICT (below each, once the
> refutation lands) is the real signal.** `notBGK=10` means "claims full orthogonality to the wall" —
> the refutation tests that claim.

## The 25 conjectures (by mechanism family)

### Metaplectic / Weil-index / Heisenberg

**`Maslov-Weil-index-mstar-congruence`** [novelty 10/notBGK 10/feasibility 3]
- *Statement:* CONJECTURE (Maslov-index parity pin). Attach to the dyadic tower μ_n ⊂ μ_{2n} ⊂ … the Weil index γ_p ∈ μ_8 (8th root of unity, the Maslov/Kashiwara cocycle of the squaring map x↦x² over Z/2^μ), a Z/8-valued 2-cocycle on the metaplectic cover. CLAIM: the over-determination depth m* (with δ* = 1−ρ−m*/n) is congruence-pinned by the Maslov index: m* ≡ s(γ_p^{(μ)}) (mod 4) where s is the signature-defe
- *Pinning mechanism:* δ* = 1−ρ−m*/n. The Maslov index is a Z/8-valued topological invariant of the triple of Lagrangian subspaces realized by (evaluation domain, its theta-dual, codeword space) — it is exactly the obstruction to a global metaplectic trivialization, hence the obstruction to the tower descent closing at the trivial depth. The congruence m* ≡ Maslov (mod 4
- *Claimed orthogonality:* The Maslov index is INVISIBLE to every moment/energy method by construction: it is a torsion (Z/8) cohomology class, while the wall M≤C√(n log m) is a real-analytic magnitude bound — the meta-theorem's three required properties (b-sensitive, archimed

**`Stone-vonNeumann-derandomization-pin`** [novelty 10/notBGK 9/feasibility 2]
- *Statement:* CONJECTURE (Stone–von Neumann de-randomization of δ*). The Heisenberg group H(Z/n) (with n=2^μ) has, by Stone–von Neumann, a UNIQUE irreducible representation of given central character; the metaplectic group Mp(2,Z/n) acts on it by intertwiners. CLAIM: the explicit dyadic RS code RS[μ_{2^μ},k] and a HAAR-RANDOM evaluation-domain code of the same parameters carry the SAME Heisenberg-module structu
- *Pinning mechanism:* The prize is exactly the EXPLICIT case (GG25/CS25 did random/folded RS to capacity; explicit dyadic RS is open). Stone–von Neumann uniqueness is the canonical de-randomization tool: any two realizations of the same Heisenberg central character are metaplectically intertwined. If the MCA bad-γ event is a function on the Heisenberg module that is int
- *Claimed orthogonality:* It compares two δ* values via a rep-theoretic ISOMORPHISM, never bounding any |η_b|; the only quantity is a Card equality under an intertwiner bijection. The meta-theorem requires a winning method to be b-sensitive/archimedean/L∞ — but this method ha

**`Weil-metaplectic-MCA-rigidity`** [novelty 9/notBGK 9/feasibility 4]
- *Statement:* CONJECTURE (Weil-equivariance pin). Let n=2^μ, q=p, RS[F_q, μ_n, k] the explicit dyadic Reed–Solomon code. The metaplectic double cover Mp(2,Z/n) acts on the pair (codeword stack, evaluation domain) by the finite oscillator/Weil representation W: the generator x↦x² (the Weil 'S' element conjugated by the squaring map) sends the MCA bad-scalar event E_δ(u₀,u₁,γ) to E_δ(W·(u₀,u₁), γ'), with γ' an ex
- *Pinning mechanism:* δ* = capacity − m*/n (the in-tree collapse law _DstarCollapseLaw; m* = smallest over-determination depth with distinct-γ union-count ≤ budget n). The metaplectic group is STRICTLY LARGER than the rotation (translation) group whose invariance is already proven (mcaEvent_rs_rotate). If the worst-direction bad-γ count is rigid under Mp(2,Z/n), then m*
- *Claimed orthogonality:* It never touches |η_b| or any moment Σ|η_b|^{2r}=q·E_r. It is a Card-of-a-Finset invariance under a finite group action on the (codeword,domain) pair — exactly the object class (MCAEquivariance) that the moment-blind meta-theorem cannot express, beca

**`WeilIndex-MultiplierWeightedFixedPoint`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* Conjecture (multiplier-weighted self-similar recursion). Let n=2^mu, p with mu_n in F_p, and for b in F_p^x set eta_b = Sum_{x in mu_n} e_p(b x). Because the squaring map sq: mu_n -> mu_{n/2} is a 2-to-1 group homomorphism with fibers {x,-x}, write eta_b = Sum_{y in mu_{n/2}} (T-twisted partial Gauss sum over the fiber of y). Define the Weil-index-weighted transfer operator on the m-tuple of norma
- *Pinning mechanism:* The exact fiberwise identity eta_b = gamma_p(b) sqrt(2) eta'_{phi(b)} is a TRUE rewriting (completing the square b x = b((x+(-x))/... ) on the antipodal fiber and applying the Weil/metaplectic transformation law for the order-2 Gauss factor), NOT an inequality. Iterating mu-1 times reduces M(n) to a base object on mu_2 (a fixed finite cyclotomic ob
- *Claimed orthogonality:* The multiplier gamma_p(b) in mu_8 is an 8th-root-of-unity automorphy factor. Every moment/energy/Wick object (E_r, A_r, the deep autocorrelation recursion) is a sum of |eta_b|^{2r}, which is BLIND to all unit-modulus phases by construction: |gamma_p 

**`Howe-dualpair-O1-Sp-branching-multiplicity-pins-mstar`** [novelty 10/notBGK 7/feasibility 2]
- *Statement:* Over F_p, the additive characters and μ_n sit inside the finite Weil representation of Sp_2(F_p); the reductive dual pair (O_1,Sp_1) (O_1={±1}=Aut of the rank-1 quadratic form x²) acts on the oscillator space, and the squaring map x↦x² is exactly the O_1-coinvariants projection. CONJECTURE: decompose 1_{μ_n}=Σ_χ m_χ·v_χ into O_1×(torus) Howe-dual isotypic components; the binding depth m* equals th
- *Pinning mechanism:* Howe duality gives a multiplicity-FREE-up-to-the-O_1-action decomposition; the branching law μ_n↓μ_{n/2} along the squaring tower is governed by an exact multiplicity formula (the number of torus weights collapsing under x↦x²), which is a COUNT OF REPRESENTATIONS, not of character-sum mass. δ* is pinned because the worst-direction list size at bind
- *Claimed orthogonality:* It counts REPRESENTATIONS (isotypic multiplicities in a Howe-dual decomposition), an object in the Grothendieck group of Sp_2(F_p)-modules, not character-sum magnitudes. The energy ladder/BGK/Wick are all moments of |η_b|; a branching multiplicity is

**`Frame-number-2adic-integrality-pin`** [novelty 9/notBGK 8/feasibility 4]
- *Statement:* Cyclotomic scheme on mu_n has Frame number F = (q^n times prod of valencies k_i) over (prod of multiplicities m_j), a positive integer. The MCA binding radius s-star(rho) is the smallest agreement dimension s for which the partial Frame quotient Phi_s = (prod of k_i for i<=s) over (prod of m_j for j<=s) first fails 2-adic integrality, i.e. where the 2-adic valuation of the multiplicity product ove
- *Pinning mechanism:* The off-Johnson binding rung is pinned by an integrality obstruction: a partial Frame quotient must be a rational integer for the scheme to fuse/quotient cleanly; the first s where the 2-adic valuation of the multiplicity product overshoots the valency product marks the binding radius. delta-star equals Johnson plus (s-star minus k)/n exactly, sinc
- *Claimed orthogonality:* Uses the Frame number, multiplicities m_j and valencies k_i (sizes of eigenspaces and cyclotomic-class cardinalities), and a 2-adic valuation test on their product: an integrality/divisibility, non-archimedean object. The wall is an analytic archimed


### Automorphic / trace-formula / QUE / L-functions

**`cat-map-QUE-rate-equidistribution-floor`** [novelty 10/notBGK 9/feasibility 2]
- *Statement:* CONJECTURE. Identify the μ_n-coset incidence dynamics on the far line with iterates of a quantized linear toral automorphism (cat map) A∈SL_2(Z/n) of order = 2-power, acting on the (Z/n)² lattice of (subset, scalar) pairs; let the depth-m binding count D*(m) = Σ over A-periodic points of period dividing 2m of a Hecke-operator matrix coefficient ⟨A^m ψ_R, ψ_R⟩ for the dyadic Hecke basis. HYPOTHESIS
- *Pinning mechanism:* D*(m) splits exactly into a Haar main term (=n, the equidistributed budget) plus a fluctuation term equal to the QUE matrix-coefficient decorrelation. δ* is pinned because m* is precisely the depth where the QUE fluctuation O(n^{1/2}θ^{-m}) crosses the O(1) budget slack: solving n^{1/2}θ^{-m*}≍1 gives m*=½log_θ n exactly. The EXACT value of δ* is t
- *Claimed orthogonality:* The object bounded is a HECKE-OPERATOR MATRIX COEFFICIENT ⟨A^m ψ,ψ⟩ of an eigenstate of the quantized dynamics — a quantum dynamical correlation, not a value of η_b and not a power-sum of η-values. The decay mechanism is the ARITHMETIC SPECTRAL GAP o

**`eichler-selberg-trace-identity-value`** [novelty 10/notBGK 9/feasibility 2]
- *Statement:* CONJECTURE. There is an EXACT Eichler-Selberg-type trace identity for the family η_b that pins M(n) as a sum of class numbers / Hurwitz numbers rather than a √-cancellation. Concretely: let A_n be the n×n circulant 'dilation transfer matrix' of the doubling map x↦x² acting on the exponents of μ_n (an order-μ automorphism of μ_{2^μ}), and let H(·) be the Hurwitz class number. CONJECTURE: Σ_{b: b∈μ_
- *Pinning mechanism:* The Eichler-Selberg trace formula equates a spectral trace (Σ over Hecke eigenvalues) with a GEOMETRIC sum over elliptic/hyperbolic conjugacy classes weighted by class numbers H(4n−t²). Our η_b family, via the self-dual maximizer and the doubling-automorphism structure of μ_{2^μ}, is exactly such a trace (η_b = trace of Frob on the dilation transfe
- *Claimed orthogonality:* A trace formula is an EXACT identity, structurally incapable of being the moment bound (which is an inequality saturated only in a limit). It uses class numbers H(4n−t²) — an arithmetic-geometric invariant (point-counts on elliptic curves / binary qu

**`DAM-IncompleteTheta-CuspAutomorphy-SquareLattice`** [novelty 9/notBGK 9/feasibility 2]
- *Statement:* Conjecture (Demirci-Akarsu-Marklof automorphy for the SQUARED incomplete theta). The in-tree refutation (_wf2ND) showed {eta_b/sqrt(n)} is Gaussian, NOT the DAM self-similar law for the LINEAR incomplete Gauss sum. Conjecture the DAM/quantum-modular law DOES hold for the QUADRATICALLY-PARAMETRIZED partial theta attached to mu_n: define Theta_N(b,p) = Sum_{0<=k<N} e_p(b * w^{k^2}) where w is a gene
- *Pinning mechanism:* For the quadratic phase k -> k^2 the partial theta sum Theta_N is a genuine incomplete Jacobi theta value, and (unlike the linear sum) it obeys the modular/quantum-modularity functional equation exactly: the metaplectic group SL_2(Z)-action renormalizes (b/p) by the continued-fraction (Gauss) map with a sqrt(N/N') contraction and a Weil-index multi
- *Claimed orthogonality:* DAM renormalization pins the value by an EXACT continued-fraction cocycle telescoping, never by a moment/sqrt-cancellation argument; the heavy DAM tail (which _wf2ND found ABSENT for the linear sum) is the signature that, on the square-residue expone

**`horocycle-escape-of-mass-winding-pins-deltastar`** [novelty 10/notBGK 8/feasibility 2]
- *Statement:* Conjecture (dyadic horocycle escape-of-mass winding). Encode the dyadic-RS agreement set as a closed orbit of the horocycle flow on the unit tangent bundle of the modular surface: the mu_n-orbit lifts to a periodic horocycle of period T(n,q) ~ n at height y = 1/q, and the agreement excess above Johnson is the WINDING NUMBER w(n,q) = net number of times this horocycle crosses the cusp neighborhood 
- *Pinning mechanism:* delta-star is pinned to a DISCRETE/RIGID invariant -- the integer winding number w(n,q) of the closed horocycle around the cusp -- which is moment-blind because it is a topological degree (an integer cohomology class), not a continuous size. The exact value delta-star = 1 - sqrt(rho) + w/n then lives on a RATIONAL LATTICE 1/n apart, and the specifi
- *Claimed orthogonality:* The pinning object is an INTEGER WINDING NUMBER (topological degree / cohomology class of the closed horocycle around the cusp), structurally incapable of being a moment or a sup-norm -- it is rigid and discrete, exactly what the moment-blind meta-th


### Monodromy / l-adic sheaves / Sato-Tate

**`KloostermanSheaf-FreqMonodromyPin`** [novelty 10/notBGK 9/feasibility 3]
- *Statement:* Conjecture (frequency field is a Kloosterman/hypergeometric sheaf trace; monodromy pins δ*). The map b↦η_b extends to b↦η_b(t)=Σ_{x∈μ_n}e_p(b x) as the trace function of an explicit ℓ-adic sheaf F on the multiplicative line (a [n]-Kummer pushforward of the Artin–Schreier sheaf — a 'monomial Kloosterman sheaf' for the map x↦x on μ_n composed with t↦t^n). HYPOTHESIS: F is geometrically irreducible w
- *Pinning mechanism:* If b↦η_b is the trace of a sheaf with full monodromy and small conductor, then by Deligne–Katz the values are equidistributed across the m cosets with discrepancy O(conductor·q^{−1/2}); the SUP over m cosets is then attained at the finitely many GALOIS-FIXED singular cosets, and m* (the over-determination depth) is the monodromy DROP integer there.
- *Claimed orthogonality:* BGK/sup-norm treats η_b as a black-box exp-sum to be cancelled. Here η_b is identified as a SHEAF TRACE and its sup is pinned by the GEOMETRIC MONODROMY GROUP and CONDUCTOR — a Galois/ℓ-adic object orthogonal to additive energy. The repo's memory rec

**`GaussSumSatoTate-FreqRestriction`** [novelty 9/notBGK 8/feasibility 4]
- *Statement:* Conjecture. Index the m=(q−1)/n cosets of μ_n in F_q^* by the multiplicative characters χ trivial on μ_n (the dual group of F_q^*/μ_n, |·|=m). Then η_b = Σ_{x∈μ_n} e_p(bx) is, by Gauss-sum expansion, η_b = (1/(q−1)) Σ_{χ: χ^? } τ(χ) χ̄(b)·G_χ(μ_n), where τ(χ) is the Gauss sum and G_χ(μ_n)=Σ_{x∈μ_n}χ(x) is the μ_n-restricted character sum (nonzero only on the n characters trivial on μ_n). Equivalen
- *Pinning mechanism:* η_b is LITERALLY a fixed unitary (DFT-of-roots-of-unity) image of the n-vector of Gauss sums (τ(χ_j)). The sup over b is the sup over the m cosets of an n-term sum of FIXED Gauss sums against VARYING unimodular phases χ̄_j(b). Katz equidistribution (a curvature/monodromy input on the Gauss-sum family — its geometric monodromy group is large) pins t
- *Claimed orthogonality:* The BGK wall bounds the sup by √-cancellation of a SINGLE additive exp-sum (the period side). Here the period side is held FIXED (the n Gauss sums τ(χ_j) are arithmetic constants, computed once) and ALL the variation is in the multiplicative phases χ


### Association scheme / Krein / pseudocyclic / fusion

**`krein-parameter-vanishing-design-threshold`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* Let E_0,...,E_d be the primitive idempotents of the cyclotomic scheme on mu_n with Krein parameters q^k_{ij} >= 0 (the dual intersection numbers, nonnegative by the Krein condition). CONJECTURE: delta* is pinned EXACTLY at the radius where the agreement-set configuration first FAILS to be a relative t-design in the dual (Q-polynomial) ordering, i.e. delta* = (1/n)*(t*(n)+1) where t*(n) is the LARG
- *Pinning mechanism:* Mutual correlated agreement at radius delta requires a family of codewords whose pairwise agreement profile realizes a specific configuration in the scheme. By the linear-programming / Delsarte duality of association schemes, such a configuration of strength t exists at a given radius IFF the dual (Krein) inner distribution is feasible, which is go
- *Claimed orthogonality:* Krein parameters are the DUAL of intersection numbers -- they live in the Q-polynomial (Bose-Mesner *idempotent*) algebra, are nonnegative INTEGERS or exact algebraic integers, and encode design/tightness, an object the L-infinity sup-norm wall has n

**`cyclotomic-number-rank-pins-distinct-gamma-fusion`** [novelty 9/notBGK 9/feasibility 4]
- *Statement:* Let C_n(F_q) be the cyclotomic association scheme on μ_n ⊆ F_q* (q=n^β, β≈4-5, n=2^μ). Its INTEGER structure constants are the cyclotomic numbers (i,j) := #{x∈μ_n : x−1 ∈ g^i μ_n, conjugate offset g^j μ_n}, equivalently the intersection numbers p_ij^k of the m=(q−1)/n-class fusion. Form the integer m×m cyclotomic-number matrix Γ = ((i,j))_{i,j}. CONJECTURE (Fusion-Rank Identity): the far-coset MCA
- *Pinning mechanism:* δ* is, in the substrate, the p-independent integer union-count |⋃_R{γ_R}| ≤ n (the distinct-γ / line-explainability count, ABF26 §4.5 far-coset face). The cyclotomic numbers (i,j) are the EXACT integer intersection data of the scheme: two far cosets γ_R, γ_S coincide on the weight-⌊δn⌋ syndrome ball iff a specific cyclotomic-number block is nonzero
- *Claimed orthogonality:* The wall M=max|η_b| is a function of the magnitudes |η_b|=√((i,i)+const); the two in-tree collapse files prove every magnitude-multiset functional renames M/√n. Γ is the INTEGER tensor (i,j), not the magnitudes: rank_{F_2}(Γ mod 2) is invariant under

**`pseudocyclic-valency-multiplicity-defect-vector-pins-delta`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* For a genuinely PSEUDOCYCLIC association scheme the multiplicities equal the valencies (m_i = k_i for all nontrivial classes) — this is the van Dam–Muzychuk characterization, and it forces a Ramanujan-tight design. The cyclotomic scheme on μ_n is almost-pseudocyclic; define the INTEGER pseudocyclic defect vector d_i := m_i − k_i ∈ ℤ (NOT the magnitude defect |η|²−n already shown field-universal in
- *Pinning mechanism:* Valencies k_i (sizes of scheme classes = coset sizes, all = m) and multiplicities m_i (dimensions of eigenspaces) are PURELY combinatorial integers from the Bose–Mesner P/Q matrices; their difference d_i measures how far the scheme is from the pseudocyclic ideal where every eigenspace is balanced. A nonzero d_i at a class means that class carries a
- *Claimed orthogonality:* The wall bounds the magnitude of one eigenVALUE; d_i is the gap between an eigenspace DIMENSION (multiplicity, an integer = trace of an idempotent) and a class SIZE (valency, an integer). Neither m_i nor k_i is a magnitude of η_b — they are integer i


### o-minimal / Zilber-Pink / André-Oort

**`o-minimal-deltastar-tameness-finite-cell`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* CONJECTURE: the threshold function (rho,t)->delta*(rho,n), t=1/log n, for explicit dyadic RS[mu_n,rho] at eps*=2^-128 (delta*=sup{delta: I(delta)<=q*eps*}), is DEFINABLE in R_{an,exp} UNIFORMLY in p=q for all p>P_0(n). By o-minimal cell decomposition the strip (1-sqrt rho, 1-rho-c*t) partitions into finitely many cells on each of which delta* is one real-analytic/semialgebraic expression with alge
- *Pinning mechanism:* delta* is the sup of a definable family (I(delta)<=q*eps* is a finite Boolean combination of polynomial inequalities in period coords exp(2 pi i k/2^mu), R_{an,exp}-definable). o-minimality => the sup is definable with finitely many non-analyticity points => delta* piecewise analytic on finitely many cells; a definable germ in the 1/log n->0 regime
- *Claimed orthogonality:* BGK is an L-infinity sup-norm ESTIMATE giving a number, never the functional FORM of the threshold. This is a TAMENESS/finiteness statement about the threshold FUNCTION, invisible to the moment-blind meta-theorem: it is not a moment of any family but

**`ZilberPink-PeriodTorusAnomalousIntersection`** [novelty 9/notBGK 9/feasibility 2]
- *Statement:* Conjecture (unlikely-intersection rigidity for the period torus). Let T_m = G_m^m be the multiplicative torus and let W ⊂ T_m be the (m−1)-dimensional subvariety cut out by the EXACT char-0 power-sum identities the Gauss-period value vector (w_1,…,w_m) satisfies over ℤ (Σw_i=−n/(q−1)·…, Σw_i^2=p−n, Σw_i^4=p(3n−3)−n^3, the in-tree coset-collapse relations), m=(q−1)/n. CLAIM: the prize sup-norm even
- *Pinning mechanism:* An over-large sup-norm value at one frequency b is an algebraic constraint w_b ∈ (large-modulus shell). Combined with the m−1 EXACT power-sum identities (which cut W to a curve once enough are imposed), a spike forces the point onto an unexpectedly small-dimensional intersection. Zilber–Pink/Bombieri–Masser–Zannier say points on W lying in anomalou
- *Claimed orthogonality:* The wall is an ANALYTIC concentration estimate: bound a sup by √(variance·log). Zilber–Pink is a DIOPHANTINE FINITENESS theorem: it says certain algebraic points are finite/bounded-height because their COORDINATES are multiplicatively dependent in an

**`Andre-Oort-special-points-pin-deltastar-CM-stratification`** [novelty 9/notBGK 5/feasibility 2]
- *Statement:* Place the family {dyadic RS code at scale 2^μ}_{μ} as a curve/variety C in a moduli/Shimura-type parameter space whose SPECIAL points correspond to scales where the code's agreement-stratification degenerates (extra collinearity / extra codewords). CONJECTURE (André-Oort form): the parameters μ at which δ*(2^μ,ρ) is NOT given by the generic closed form 1 − √ρ + (g(ρ))/n — i.e. the SPECIAL scales —
- *Pinning mechanism:* André-Oort (proven for A_g, Pila-Tsimerman; o-minimal) states the special points (CM points) on a subvariety are a FINITE union of special subvarieties — an exact, effectively-finite set. The mechanism reframes the SCALE-dependence of δ* as a moduli problem: δ* is a piecewise-algebraic function of the scale parameter that is GENERICALLY constant (i
- *Claimed orthogonality:* The pinning is by a FINITENESS-of-special-points theorem (André-Oort), which localizes ALL possible anomalous behavior to a finite, listable set of special scales — orthogonal to bounding any exponential sum at the prize scale, because the argument i


### Proof complexity / SoS / nullcone

**`DMO-nullcone-orbit-degree-relation-module`** [novelty 9/notBGK 9/feasibility 2]
- *Statement:* Conjecture (Dvir–Mehta–Oliveira orbit-degree of the relation module). Consider the F_p[μ_n]-module Rel_{r} of F_p-linear relations among the depth-r dilation-twisted Gauss periods, viewed as a point in the affine space of (2r)-tensors via the moment map. Let the algebraic group G = F_p^× × Aut(μ_n) (dilation × Galois) act. DMO (Derksen–Makam / Dvir–Mehta–Oliveira null-cone theory) attaches to this
- *Pinning mechanism:* The char-0 coset locus (V_r=2^{n/2^{⌊log₂r⌋+1}} solutions) is the STABLE orbit of the dilation×Galois action. The char-p spurious solutions are EXTRA solutions that appear only mod p. The DMO/null-cone claim is that these extras are precisely the UNSTABLE points (orbit-closure boundary) of the same action, with bounded separation degree δ₀. Semicon
- *Claimed orthogonality:* This is a GEOMETRIC-INVARIANT-THEORY object (null-cone, orbit-closure, Hilbert–Mumford stability degree), not a magnitude. The BGK wall lives in the SCALAR ‖·‖_∞ of a character sum; DMO degree lives in the INVARIANT RING of a group action on a tensor

**`Fourier-SoS-degree-asymmetry-transition`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* Constant-degree Fourier SoS feasible below Johnson and above capacity; first-infeasible delta = delta* = 1-rho-Theta(1/log n).
- *Pinning mechanism:* Phase transition; char-p antipodal-identity SoS degree jumps (char-0 deg 2, char-p higher by splitting).
- *Claimed orthogonality:* Pseudoexpectation = PSD functional not a sum; IMP-2023 Fourier-SoS separates from energy; pin is the degree jump.


### p-adic / Swan conductor / valuation

**`Swan-break-valuation-deltastar`** [novelty 9/notBGK 9/feasibility 2]
- *Statement:* Define the local break-multiset (Swan/slope decomposition) of the convolution sheaf M_r = F_b^{*r} at its two singular points {0, infinity} on P^1 (F_b = [t->t^m]^* L_psi). FKM/Katz break-rigidity conjecture (this angle): delta* in the prize regime is pinned by the p-ADIC valuation/break-jump pattern, NOT the rank: specifically delta* = 1 - rho - m*/n where m* = min{ r : the break decomposition of
- *Pinning mechanism:* The Swan conductor / break decomposition is a p-ADIC (l-adic local-monodromy) invariant: it is an exact non-negative rational read from the wild inertia action, totally independent of the archimedean SIZE of any character sum. For a TAME sheaf the Euler-Poincare / Grothendieck-Ogg-Shafarevich count is EXACT (chi_c = rank·(2-2g-#sing) with Swan=0), 
- *Claimed orthogonality:* Swan conductors and break slopes are WILD-INERTIA (p-adic) invariants: rational numbers measuring ramification, with no archimedean content whatsoever. The energy/BGK wall lives in the COMPLEX magnitude of eta_b (an archimedean L-infinity object the 

**`Swan-conductor-jump-at-binding-radius`** [novelty 10/notBGK 7/feasibility 3]
- *Statement:* For each far-frequency b, consider the pullback sheaf F_b = [x -> b x]^* L_chi^{(n)} on G_m, where L_chi^{(n)} is the rank-1 sheaf whose local system encodes the mu_n indicator (a tame Kummer sheaf twisted by the additive character psi via the [n]-pushforward). Define the LOCAL SWAN CONDUCTOR profile s_b(t) = Swan_infinity(F_b ⊗ (twist by the order-t dilation character)) as t runs over the index l
- *Pinning mechanism:* The worst frequency saturates precisely when the local monodromy at infinity transitions from tame (sqrt-p cancellation holds, agreement stays at capacity) to wild (cancellation degrades, agreement binds). This onset is a ramification-theoretic INTEGER (a break/slope of the local representation), read off from the Hasse-Arf / break-decomposition of
- *Claimed orthogonality:* The Swan conductor is a VALUATION/ramification invariant (a p-adic slope of the local Galois representation), categorically NOT a magnitude. The L-infinity / energy / moment method is provably blind to it: two sheaves with identical |trace| profiles 


### Frequency-side restriction / decoupling

**`FourierDimFreqField-RestrictionGap`** [novelty 9/notBGK 9/feasibility 3]
- *Statement:* Conjecture (frequency-field Fourier dimension forces the exact gap). View the normalized frequency field f: F_q^*/μ_n → C, f(b̄)=η_b/√n (well-defined on cosets). Its multiplicative Fourier coefficients are f̂(χ)=τ(χ)/√q·1[χ|μ_n=1] — supported on EXACTLY n characters, each of modulus 1. HYPOTHESIS (a Mockenhaupt–Tao restriction/extension estimate for the MULTIPLICATIVE group F_q^*/μ_n ≅ Z/m): the m
- *Pinning mechanism:* The frequency field's multiplicative spectrum is supported on the index-m SUBGROUP {χ: χ|μ_n=1} with all coefficients unimodular (Gauss-sum normalization |τ(χ)|=√q). A restriction estimate for a SUBGROUP support is exact (no √-loss — subgroups are the equality case of Mockenhaupt–Tao on Z/m), so the L^∞ norm of f is pinned algebraically by the n un
- *Claimed orthogonality:* BGK/energy bounds the sup of an ADDITIVE exp-sum on μ_n. This routes entirely through the MULTIPLICATIVE Fourier transform on F_q^*/μ_n ≅ Z/m, where the spectrum is a SUBGROUP (the μ_n-annihilator) with unimodular weights — the equality/exact case of

**`FreqDecoupling-CosetCurvatureModuli`** [novelty 9/notBGK 8/feasibility 3]
- *Statement:* Conjecture (ℓ^2 decoupling on the frequency cosets). Partition the m=(q−1)/n cosets b·μ_n into dyadic blocks indexed by the 2-adic valuation v_2(ind(b)) of the discrete log of b (the FRI/STARK valuation filtration). For a smooth weight w on F_q define the frequency-extension operator E_freq g (x) = Σ_b g(b) η_b e_p(−bx). HYPOTHESIS: the curve b↦η_b, as b ranges over a single μ_n-coset of the multi
- *Pinning mechanism:* Decoupling on the frequency curve converts the m-fold sup into a block-orthogonal ℓ^2 sum over O(log m) dyadic valuation blocks, each of size controlled by curvature. Because the curve is nondegenerate (curvature input), the blocks are nearly orthogonal and the sup is forced to the √(n·#blocks)=√(n log m) scale with EXACT constant 1 (not C), pinnin
- *Claimed orthogonality:* The repo's no-go explicitly states decoupling is dead on the PERIOD side because μ_n is 0-dimensional/flat (no curvature, wrong norm: decoupling outputs L^{2r} moments). Here decoupling is applied to the FREQUENCY field b↦η_b, which is NOT 0-dimensio


### Dynamics / odometer / Birkhoff

**`OdometerSignLaw-BirkhoffAverage`** [novelty 9/notBGK 9/feasibility 2]
- *Statement:* Index the dilation orbit of b by k in Z/m via b_k = g^k * b0. CONJECTURE: the period sign s_{b_k}(i) is given by an EXPLICIT 2-adic substitution / odometer cocycle: there is a fixed finite-state map phi: (Z/2^mu) x {+,-} -> {+,-} such that s_{b_k}(i) = phi-orbit value determined by the 2-adic digits of k*(p-1)/n, making i -> s(i) the Birkhoff orbit of a minimal odometer (adding-machine) rotation o
- *Pinning mechanism:* An odometer (adding machine on Z/2^mu, the natural dynamics of the 2-power tower since going mu_{2^i}->mu_{2^{i+1}} is literally a +1 carry in the 2-adic digit of the dilation index) is UNIQUELY ERGODIC and MINIMAL: every orbit equidistributes deterministically with an EXACT (not random) large-deviation rate for run-lengths of any cylinder. Identif
- *Claimed orthogonality:* Odometer dynamics is DETERMINISTIC and ARCHIMEDEAN (a uniquely-ergodic adding machine), and the run-length large-deviation it produces is an EXACT ergodic-average statement, NOT the probabilistic-EVT the meta-theorem forbids (periods-are-exchangeable

## Adversarial refutation verdicts

**RESULT: all 25 reduced to the BGK wall — `{REDUCES-TO-BGK: 25}`.** Triple-killed across the three lenses:
- **reduce-to-BGK lens: 25/25 REDUCES-TO-BGK** (every conjecture's pinning device re-enters the char-p √-cancellation)
- **reduce-to-Johnson lens: 22/25 REDUCES-TO-JOHNSON** (+1 BGK, +2 refuted) — most pin only the far-line Plotkin proxy
- **countermodel lens: 25/25 REFUTED-FALSE** (each contradicts an in-tree axiom-clean fact, the meta-theorem, the p-independence smoking-gun, or is window-vacuous)

This exactly reproduces the campaign prior (79+ conjectures → 0 survivors). **No survivor.**

### Per-conjecture verdict table

| conjecture | notBGK | reduce-BGK | reduce-Johnson | countermodel |
|---|---|---|---|---|
| `Maslov-Weil-index-mstar-congruence` | 10 | →BGK | →Johnson | FALSE |
| `cat-map-QUE-rate-equidistribution-floor` | 9 | →BGK | →Johnson | FALSE |
| `KloostermanSheaf-FreqMonodromyPin` | 9 | →BGK | →Johnson | FALSE |
| `Stone-vonNeumann-derandomization-pin` | 9 | →BGK | →Johnson | FALSE |
| `eichler-selberg-trace-identity-value` | 9 | →BGK | →Johnson | FALSE |
| `krein-parameter-vanishing-design-threshold` | 9 | →BGK | →Johnson | FALSE |
| `o-minimal-deltastar-tameness-finite-cell` | 9 | →BGK | →Johnson | FALSE |
| `FourierDimFreqField-RestrictionGap` | 9 | →BGK | →Johnson | FALSE |
| `Swan-break-valuation-deltastar` | 9 | →BGK | FALSE | FALSE |
| `DMO-nullcone-orbit-degree-relation-module` | 9 | →BGK | →Johnson | FALSE |
| `Weil-metaplectic-MCA-rigidity` | 9 | →BGK | →Johnson | FALSE |
| `Fourier-SoS-degree-asymmetry-transition` | 9 | →BGK | →Johnson | FALSE |
| `ZilberPink-PeriodTorusAnomalousIntersection` | 9 | →BGK | →Johnson | FALSE |
| `cyclotomic-number-rank-pins-distinct-gamma-fus` | 9 | →BGK | →Johnson | FALSE |
| `pseudocyclic-valency-multiplicity-defect-vecto` | 9 | →BGK | →Johnson | FALSE |
| `OdometerSignLaw-BirkhoffAverage` | 9 | →BGK | →Johnson | FALSE |
| `WeilIndex-MultiplierWeightedFixedPoint` | 9 | →BGK | FALSE | FALSE |
| `DAM-IncompleteTheta-CuspAutomorphy-SquareLatti` | 9 | →BGK | →Johnson | FALSE |
| `horocycle-escape-of-mass-winding-pins-deltasta` | 8 | →BGK | →Johnson | FALSE |
| `Howe-dualpair-O1-Sp-branching-multiplicity-pin` | 7 | →BGK | →Johnson | FALSE |
| `GaussSumSatoTate-FreqRestriction` | 8 | →BGK | →BGK | FALSE |
| `Frame-number-2adic-integrality-pin` | 8 | →BGK | →Johnson | FALSE |
| `Andre-Oort-special-points-pin-deltastar-CM-str` | 5 | →BGK | →Johnson | FALSE |
| `Swan-conductor-jump-at-binding-radius` | 7 | →BGK | →Johnson | FALSE |
| `FreqDecoupling-CosetCurvatureModuli` | 8 | →BGK | →Johnson | FALSE |

### The recurring reduction pattern (why the wall is irreducible)

Every novel framing follows the **same canonical collapse**: it dresses the binding-depth
SELECTOR `m*` (with `δ* = 1−ρ−m*/n`) in a topological / spectral / arithmetic invariant —
but the *integer value* of `m*` is set by **where the orbit-count / distinct-γ growth law
`O(c)` collapses to ≤2**, and that growth law at depth `r≈ln q` **IS** the char-p additive
energy `E_r(μ_n) ≤ (2r−1)‼·n^r` = the BGK/Paley wall. A torsion/topological invariant (Maslov
`Z/8`, monodromy drop, Krein parameter) can at most select a *residue class* of `m*`; pinning
the *unique integer* requires the budget crossing = the energy/wall. The sharpest kills:
- **cat-map QUE**: the "quantized Hecke operator" on the coset lattice **is** the abelian
  Paley/Cayley convolution operator (`_PaleyCayleyEigenvalue.cayley_eigenvalue_eq_eta`,
  rfl-level), diagonalized by additive characters with eigenvalue exactly `η_b` — so its
  spectral gap *is* `M(n)`, the wall verbatim.
- **Kloosterman-sheaf monodromy**: identical to the already-built `MonodromyConductorScaffold` —
  the conductor RELOCATES (does not remove) the wall.
- **Maslov index / metaplectic / Stone–von Neumann**: the intertwiner is *forced to be* the
  Gauss-period sup-norm; the wall re-enters at the metaplectic action, plus the `Z/8` class
  cannot pin a `p`-independent integer (smoking-gun `D=89` across 4 primes).
- **countermodel (all 25)**: each is window-vacuous or contradicts the proven p-independence /
  the white-noise period covariance / the meta-theorem.

### Honest conclusion

**0 survivors of 25** — the most novel, most deliberately-orthogonal conjectures the campaign
could generate (across 9 mechanism families, novelty-vetted, dead-lanes banned) *all* reduce to
the BGK wall. This is not a failure of imagination but **strong positive evidence the wall is
structurally irreducible**: the binding depth `m*` is a *magnitude* (the energy crossing), and no
torsion / spectral-gap / equidistribution-rate / rigidity *dressing* can pin a magnitude without
re-invoking the √-cancellation. The genuine open prize remains the single char-p BGK input;
an escape, if one exists, must defeat this collapse pattern — it cannot merely relabel `m*`.

## Honest framing

These are **exploration-grade conjectures** (the honesty contract: bold in exploration, strict in
proof-claims). Several are almost certainly false or reduce to the wall — that is the *expected* outcome
and refuting them is the productive work. A conjecture that **SURVIVES** all three lenses is a genuine,
rare lead worth formalizing as a named open `Prop`; one that reduces shows *exactly where* the wall is
unavoidable. None closes δ* — the exact value remains the single open char-p BGK input.
