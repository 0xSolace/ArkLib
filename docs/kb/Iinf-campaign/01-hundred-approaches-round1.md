# Attacking I_∞(δ) — Round 1: 100 approaches, then shot down, then revised 100

## The target (exact)
`I_∞(δ)` = the saturated (n-independent at fixed δ), **q-independent**, char-0 worst-case far-line
monomial incidence over `μ_{2^a}` (n=2^a-th roots of unity). Concretely (cleanest direction `dir(k+1,k+2)`):
`I_∞ = #{ −e_1(S) : S ⊆ μ_n, |S|=w=(1−δ)n, e_2(S)=0 }`, equivalently (Fourier form)
`#{ f̂(1) : A ⊆ ℤ/n, |A|=w, f̂(j)²=f̂(2j) ∀ odd j }`, `f̂(j)=Σ_{a∈A} ω^{ja}`, `ω=e^{2πi/n}`.
**GOAL:** bound `I_∞(δ)`'s growth as `δ→1−ρ` (capacity); show it crosses `n` exactly at the window edge
`δ* = 1−ρ−Θ(1/log n)`. Worst case included. Must NOT reduce to an open quantity; must close to proven math.

---

## ROUND 1 — 100 approaches (raw, bold, unfiltered)

### A. Additive combinatorics (1–10)
1. Plünnecke–Ruzsa on the value-set `{e_1(S)}` as an iterated sumset of `μ_n`.
2. Freiman 3k−4 / structure theorem: the e_2=0 variety has small doubling ⟹ contained in a GAP.
3. Balog–Szemerédi–Gowers: many γ-coincidences ⟹ a large additive-energy substructure to bound.
4. Croot–Lev–Pach / polynomial method (cap-set style) on the e_2=0 constraint over ℤ/n.
5. Kelley–Meka density-increment for the 3-term structure in the constraint set.
6. Sárközy / Bourgain on sumsets of dilates (the directions are dilates of μ_n).
7. Schur-like / Rado regularity of the symmetric-function equations.
8. Sidon/B_h set theory: e_2=0 subsets as B_h configurations, count via B_h extremal bounds.
9. Sanders' quasi-polynomial Bogolyubov on the constraint variety.
10. Additive-energy tensor power trick: bound `I_∞^t` to get `I_∞`.

### B. Polynomial method / algebraic (11–20)
11. Combinatorial Nullstellensatz: the γ-values are roots of an explicit low-degree polynomial.
12. Schwartz–Zippel on the (w−k−1)-codim symmetric-function variety to bound its image.
13. Resultant elimination: γ = root of `Res_{e_i}(constraints)`, bound deg of the eliminant.
14. Generalized Vandermonde / Schur polynomial nonvanishing patterns control the count.
15. Newton's identities to reduce e_2=0,… to power sums p_j, then count power-sum solutions.
16. Alon–Tarsi / permanent-determinant for the incidence count.
17. The "method of multiplicities" (Dvir–Kopparty–Saraf–Sudan) on μ_n.
18. Stepanov auxiliary polynomial vanishing on all γ to high order.
19. Wronskian / confluent Vandermonde rank bounds the number of close codewords.
20. Bezout on the intersection of the symmetric-function hypersurfaces.

### C. Fourier / harmonic analysis on ℤ/n (21–30)
21. Uncertainty principle (Tao for ℤ/p, Meshulam for ℤ/n) on the f̂(j)²=f̂(2j) support.
22. Gowers U^k norms: the constraint set has bounded U^2/U^3 norm ⟹ pseudorandom ⟹ count.
23. The f̂(j)²=f̂(2j) recursion as a multiplicative-by-2 dynamical constraint on the spectrum.
24. Bohr-set / Bourgain-systems structure of the e_2=0 set.
25. Restriction/extension estimates for the cyclotomic "sphere" {f̂(j)²=f̂(2j)}.
26. Decoupling (Bourgain–Demeter) for the moment curve realized by (f̂(1),f̂(2),…).
27. The constraint = an autocorrelation condition; bound via Wiener/Beurling.
28. Hardy–Littlewood circle method for the count of solutions to the symmetric equations.
29. Fourier dimension / Salem-set heuristics for the constraint variety.
30. The 2-adic Fourier (Walsh) transform diagonalizes the ×2 map; read off the count.

### D. Geometry of numbers / lattices / heights (31–38)
31. Minkowski's 2nd theorem on the agreement lattice (successive minima of the RS dual).
32. Mahler measure / Lehmer lower bounds force γ-values apart, capping their number.
33. The γ-values are S-units; bound via the S-unit equation finiteness (Evertse–Győry).
34. Subspace theorem (Schmidt) on the linear forms defining the γ-locus.
35. Bogomolov / equidistribution of small points on the cyclotomic variety.
36. Successive-minima transference for the dual of the constraint lattice.
37. Arakelov height of the γ-cycle; bound the degree via an arithmetic Bezout.
38. Lattice-point counting (Ehrhart) for the Newton polytope of the constraint.

### E. Algebraic geometry / toric / tropical / motivic (39–46)
39. Tropicalize the constraint; the γ-count ≤ tropical stable-intersection number.
40. Toric intersection theory on the cyclotomic toric variety (μ_n = torus orbit).
41. Motivic / point-counting: |variety(F_q)| as a motive, the count is q-independent ⟹ Euler char.
42. The constraint variety's genus/Betti numbers bound the γ-count (Weil, but char-0/topological).
43. Hodge theory of the cyclotomic configuration space; the count = a Hodge number.
44. Bernstein–Kushnirenko mixed volume of the symmetric-function Newton polytopes.
45. Resolution of singularities of the e_2=0 variety; count via the resolved fibers.
46. Intersection cohomology / perverse sheaves on the symmetric-product Sym^w(μ_n).

### F. Extremal & probabilistic combinatorics (47–54)
47. Hypergraph container method: the e_2=0 subsets live in few containers ⟹ few γ.
48. Shearer / entropy compression bound on the number of valid S.
49. Turán-type: the constraint graph (S vs e_2=0) has bounded independence ⟹ count.
50. The Lovász Local Lemma / Moser–Tardos to count constraint solutions.
51. Dependent random choice for the agreement structure.
52. Removal lemma (graph/hypergraph) for the cyclotomic constraint triples.
53. Spread / fractional-relaxation (Park–Pham) for the antipodal-config count.
54. Junta / influence bounds (FKN, KKL) on the indicator of valid S.

### G. Cyclotomic / Galois / group-ring (55–62)
55. Mann/Lam–Leung exact vanishing-sum structure ⟹ S antipodally-built ⟹ direct count.
56. Galois descent: γ-values form Gal(ℚ(ζ_n)/ℚ)-orbits of bounded size.
57. Group-ring ℤ[ℤ/n]: the constraint is an ideal; count = quotient dimension.
58. Stickelberger / Jacobi-sum factorization constrains the e_i(S).
59. The ×2 Frobenius (2-power) acts on the spectrum; orbits bound the count (Artin–Schreier flavor).
60. Iwasawa-theoretic tower of the μ_{2^a} flag bounds the count level-by-level.
61. Brauer / character-table relations among the symmetric functions.
62. The constraint as a representation of the dihedral/2-group symmetry of μ_{2^a}.

### H. Generating functions / analytic combinatorics / transfer matrix (63–69)
63. Transfer-matrix on the ℤ/n cyclic structure: I_∞(δ) = trace of a power.
64. Symbolic/ordinary generating function for #{S : e_2(S)=0} graded by e_1.
65. Saddle-point / singularity analysis (Flajolet–Sedgewick) of the GF for the growth law.
66. Species theory / exponential GF for the antipodal-pair-decorated structures.
67. The count as a constant term (CT) of a Laurent expansion; MacMahon Ω-calculus.
68. q-series / partition-theoretic identity for the antipodal subset count.
69. WZ / creative telescoping to find a closed recurrence for I_∞(δ).

### I. Dynamical systems / ergodic (70–75)
70. The ×2 map on ℤ/2^a is a Bernoulli shift; the constraint = a subshift of finite type, count its words.
71. Ergodic / Furstenberg correspondence for the multiplicative-recurrence constraint.
72. Symbolic dynamics: valid S = paths in a de Bruijn-like graph; count via its adjacency spectrum.
73. Thermodynamic formalism: I_∞(δ) = exp(topological pressure) of the constraint dynamics.
74. Renormalization of the 2-power tower (self-similar) for the growth exponent.
75. Equidistribution of the ×2 orbit closures bounds the value-set.

### J. Spectral / graph / expander (76–81)
76. The incidence bipartite graph (S, γ); I_∞ = its max matching / spectral radius.
77. Cayley graph of ℤ/n with the constraint connection set; eigenvalue count.
78. Expander mixing lemma on the constraint graph bounds the γ-count.
79. Interlacing (Cauchy) for the constraint submatrix eigenvalues.
80. Kazhdan property (T) / spectral gap of the acting group bounds clustering.
81. The constraint as a quantum graph / Schrödinger operator; count = bound states.

### K. Logic / model theory / o-minimality (82–86)
82. o-minimality: the family {valid S} is definable with uniformly bounded #components ⟹ I_∞ bounded.
83. The count is a definable function of δ; cell decomposition gives its growth.
84. Ax–Grothendieck / ultraproduct transfer of a char-0 bound to all n.
85. VC-dimension of the constraint family ⟹ Sauer–Shelah polynomial count.
86. Tame geometry (Pila–Wilkie) counting rational/algebraic points on the constraint.

### L. Computer science / SOS / complexity / coding (87–93)
87. Sum-of-squares / Positivstellensatz certificate that #γ ≤ Cn.
88. Matrix rigidity of the cyclotomic Vandermonde bounds the close-codeword count.
89. Communication complexity / rank lower bound for the incidence matrix.
90. The count as #SAT of a structured CNF; treewidth/branchwidth bound.
91. Coding: the γ-values = low-weight words in a cyclic code coset; weight enumerator bound.
92. List-decoding meta: bound I_∞ by the list size of an auxiliary explicit code.
93. Information-theoretic Plotkin/Singleton-type counting on the agreement structure.

### M. Physics / statistical mechanics / quantum (94–98)
94. Partition function of an Ising/Potts model on ℤ/n whose ground states = valid S.
95. Bethe ansatz / integrability of the symmetric-function constraint (it's a free-fermion-like sum).
96. Coulomb gas / log-gas on the unit circle (roots of unity) for the e_1 distribution.
97. Quantum Fourier / stabilizer formalism: μ_{2^a} is a stabilizer state, count = a stabilizer rank.
98. Random-matrix universality of the cyclotomic period operator (made rigorous via the moment method).

### N. Wild / alien (99–100)
99. Category-theoretic: I_∞ as a colimit/Kan extension over the subgroup tower; bound via adjunction.
100. Topological data analysis / persistent homology of the point cloud {e_1(S)}; the count = a Betti number.

---

## SHOOT-DOWN — the recurring fatal failure modes (Round-1 triage)
Define the failure tags. Each Round-1 approach fails ≥1:
- **[GP]** secretly reduces to the Gauss-period/char-sum sup or additive-energy/sumset (the open core) — forbidden.
- **[J]** only reaches the Johnson radius / a second-moment-strength bound, not past Johnson.
- **[VAC]** vacuous at the prize scale (works only for small n or needs n≫p or n≪log p).
- **[INC]** the bounding quantity is itself incomputable / not effectively boundable (e.g. an unproven height bound).
- **[GEN]** the tool needs genericity / random structure that μ_{2^a}'s exact antipodal structure violates.
- **[∞]** the natural bound is the trivial `≤ C(n,w)` or `≤ q` (exponential / no saving).
- **[SUP]** computes an AVERAGE/moment, cannot pin the MAX/sup (the worst-case incidence).
- **[NA]** the field's theorem doesn't actually apply (wrong category; a slogan, not a mechanism).

### Triage (cluster-level; per-item in the essays)
- A1,A3,A6,A10 → **[GP]** (Plünnecke/BSG/energy power trick are exactly the additive-energy = open core).
- A2,A9 (Freiman/Sanders) → **[VAC]** (the doubling is large; structure theorems need small doubling).
- A4,A5 (Croot-Lev-Pach/Kelley-Meka) → **[NA]/[J]** (designed for 3-AP-free density, not this count).
- A7,A8 (Rado/B_h) → **[J]** (B_h ↔ energy r-bound ↔ Johnson).
- B11,B13,B20 (Nullstellensatz/resultant/Bezout) → the right SHAPE but the degree bound is **[∞]** (deg ~ C(n,w)).
- B12,B14,B16 → **[∞]** (Schwartz-Zippel/permanent give the trivial count).
- B15,B17,B18,B19 (power sums/multiplicities/Stepanov/Wronskian) → **[J]** (cap at Johnson, the in-tree wall).
- C21 (uncertainty) → **[J]** (the configs are NOT uncertainty extremizers, verified this session).
- C22,C26 (Gowers/decoupling) → **[GP]** (the U^k norm IS the higher additive energy = open core).
- C23,C30 (×2 dynamical / Walsh) → promising STRUCTURE but no bound yet → keep, refine.
- C24,C25,C27,C28,C29 → **[GP]** (Bohr/restriction/circle-method = character sums = open core).
- D31,D36 (Minkowski/transference) → **[VAC]** (λ_1 = n−k+1 ok but λ_2 prime-sensitive ~ p^{1/d}).
- D32,D33,D37 (Mahler/S-unit/Arakelov) → **[INC]/[VAC]** (heights are prime-sensitive or ineffective at scale).
- D34 (Subspace thm) → **[INC]** (ineffective; constant not explicit).
- D35,D38 (Bogomolov/Ehrhart) → **[NA]/[∞]**.
- E39,E44 (tropical/mixed-volume) → **[GEN]** (sharp only for generic coeffs; μ_n non-generic, surplus = energy).
- E40,E45 (toric/resolution) → **[NA]** (no effective count emerges).
- E41,E42,E43,E46 (motivic/Hodge/IC) → **[NA]/[∞]** (beautiful but no quantitative bound).
- F47,F53 (containers/spread) → promising; risk **[∞]** if container count is large → keep, refine.
- F48,F49,F50,F51,F52,F54 → **[J]/[NA]** (entropy/LLL/removal give weak or wrong-shape bounds).
- G55 (Mann/Lam-Leung) → the CORE TRUTH but only gives the char-0 STRUCTURE, not the COUNT growth → keep, refine.
- G56,G59,G60 (Galois/Frobenius/Iwasawa) → promising orbit structure; risk **[SUP]** → keep, refine.
- G57,G61,G62 (group-ring/Brauer/rep) → **[∞]** (quotient dim is the trivial count).
- G58 (Stickelberger) → **[VAC]** (√p-scale, this session's K3).
- H63,H69 (transfer-matrix/WZ) → promising; the matrix is n×n, spectral radius unknown → keep, refine.
- H64–H68 (GF/saddle/species/CT/q-series) → promising STRUCTURE; need the GF first → keep, refine.
- I70,I72,I73,I74 (SFT/symbolic/pressure/renorm) → promising self-similar angle → keep, refine.
- I71,I75 (Furstenberg/equidistribution) → **[GP]** (equidistribution = the open core).
- J76,J77,J79 (incidence graph/Cayley/interlacing) → **[SUP]/[J]** (spectral = second moment = Johnson).
- J78,J80,J81 → **[GP]/[NA]** (expander mixing = char sum; property T = NA).
- K82,K83,K85 (o-minimality/VC) → promising UNIFORMITY angle but **[NA]** over finite fields (not o-minimal).
- K84 (Ax–Groth/ultraproduct) → promising transfer; risk **[NA]** (transfers truth not bounds) → keep, refine.
- K86 (Pila–Wilkie) → **[NA]** (counts rational points, not this).
- L87 (SOS) → promising; risk **[GP]** (the SOS gap = spectral = Gauss period) → keep but wary.
- L88,L89,L90 (rigidity/CC/treewidth) → **[∞]/[J]**.
- L91,L92,L93 (cyclic-code/list/Plotkin) → **[J]/[GP]** (circular: list IS the object).
- M94,M95,M96 (Ising/Bethe/Coulomb) → promising integrable/log-gas STRUCTURE → keep, refine.
- M97,M98 (stabilizer/RMT) → **[SUP]/[NA]** (RMT universality is exactly the open equidistribution).
- N99,N100 (category/TDA) → **[NA]** (no quantitative bound).

**Net Round-1:** ~70 die (GP/J/VAC/INC/NA/∞/SUP). ~30 carry a genuine STRUCTURAL idea worth refining:
the **×2-dynamical/self-similar** (C23,C30,I70,I72,I73,I74), the **exact-Mann count** (G55,G56,G59,G60),
the **container/spread** (F47,F53), the **generating-function/transfer-matrix** (H63–H69), the
**integrable/log-gas** (M94,M95,M96), the **uniformity/transfer** (K84), and **SOS** (L87, wary).

---

## ROUND 2 — revised 100 (each AVOIDS the tagged failure mode of its parent)
**Design rule for Round 2:** every approach must (i) stay q-INDEPENDENT & char-0 (avoid GP), (ii) target the
COUNT/growth not a moment (avoid SUP/J), (iii) be effective at prize scale (avoid VAC/INC), (iv) exploit the
EXACT 2-power/antipodal structure (turn GEN into a feature), and (v) yield a sub-exponential count (avoid ∞).
They cluster around the 6 surviving structural seeds, deepened and made concrete.

### R-α. ×2-dynamical / self-similar count (101–116) [from C23,C30,I70,I72,I73,I74]
101. Model valid A⊆ℤ/2^a by the SFT of the ×2 (doubling) map on the binary `a`-tuple addresses; I_∞ = #words.
102. The f̂(j)²=f̂(2j) (odd j) relation is a COCYCLE over the ×2 map; count cocycle solutions via its transfer operator's leading eigenvalue (a FIXED finite matrix, n-independent) — gives the saturation directly.
103. Build the explicit `2×2` (or `O(1)×O(1)`) transfer matrix `T` for the per-bit antipodal constraint; I_∞(δ) = (row vec)·T^a·(col vec); growth = λ_max(T), an algebraic number computed once.
104. Renormalization-group fixed point of the fold x↦x² acting on the constraint measure; the growth exponent is the RG eigenvalue at the fixed point (self-similarity proven, not assumed).
105. Subshift entropy: `log I_∞(δ)/a → h(δ)` = topological entropy of the constraint subshift; compute h(δ) exactly via the SFT adjacency spectrum and show h crosses `log... ` at the window edge.
106. Dyadic martingale / branching: valid A as a 2-adic tree; the count = a branching-process expectation with EXACTLY computable per-level offspring (antipodal split), giving a closed product formula.
107. The constraint is a 2-automatic sequence in `a`; by Christol/Cobham the GF is algebraic over F_2(X) — extract the growth from the algebraic equation.
108. Skew-product over the odometer (×2 on ℤ_2): I_∞ = a cocycle dimension, bounded by the odometer's discrete spectrum.
109. Cellular-automaton (rule on the bit-address) whose invariant configs = valid A; count via the CA's directional entropy.
110. The fold gives `I_∞(δ) = Σ_strata F(I_∞(δ'))` with δ'=fold of δ; SOLVE the functional equation in closed form (this is the missing fold recursion done at the COUNT level, not the codeword level).
111. Mahler-equation / Mahler-functional-equation `I(X²)=R(X)·I(X)` for the GF (2-power ⟹ Mahler function); the singularity structure gives the growth.
112. Furstenberg ×2,×3-style rigidity REPLACED by ×2-only EXACT structure: classify the ×2-invariant constraint sets (finite list), count each.
113. Transfer-operator (Ruelle) determinant; I_∞(δ) = leading zero, computed via the dynamical zeta function (rational for the SFT).
114. Wang-tiling / aperiodic-order count of the antipodal configurations as a 1D tiling; matching rules ⟹ finite transfer matrix.
115. The `f̂(j)²=f̂(2j)` orbit structure under ×2 partitions odd j into 2-adic chains; count = product over chains of a per-chain finite count.
116. Bratteli diagram of the μ_{2^a}-tower; I_∞ = a dimension-group trace, an algebraic invariant.

### R-β. Exact-Mann antipodal enumeration (117–130) [from G55,G56,G59,G60]
117. Mann/Lam–Leung: e_2(S)=0 ⟺ the product-multiset {s_is_j} is antipodally balanced ⟺ `r_2(t)=r_2(t+n/2)`; ENUMERATE the balanced-difference configs directly by an exact bijection to pair-partitions.
118. Parametrize valid A by its antipodal-pairing graph; I_∞ = #graphs × (free e_1 per graph), a clean product.
119. Galois-orbit reduction: the γ-values are Gal-conjugate in bounded-degree extensions; I_∞ = #orbits × deg, count #orbits combinatorially.
120. The 2-adic Frobenius (squaring) orbits the spectrum; valid A = unions of Frobenius-orbits, count via the orbit-length distribution (exact for 2-power).
121. Exact inclusion–exclusion over the antipodal-pair lattice (the n/2 pairs form a Boolean lattice); Möbius-invert the count.
122. The constraint variety is a UNION of linear cyclotomic subspaces (antipodal cosets); count the distinct e_1-images of the subspaces (finite, explicit).
123. Necklace/Burnside count of the antipodal configs under the dihedral symmetry of μ_{2^a}.
124. The e_1-value-set of antipodal-balanced A = a SUBGROUP-coset structure in ℤ[ζ]; its cardinality is a cyclotomic index, computed via the different/conductor.
125. Lam–Leung gives the EXACT energy `(2r−1)!!n^r` at r=2 region; bootstrap to the COUNT via the energy-to-count inequality made EXACT for antipodal sets (no √-loss because the structure is rigid).
126. Polynomial-ring quotient `ℤ[ζ]/(antipodal ideal)`: I_∞ = dim of a graded piece, an explicit Hilbert-series coefficient.
127. The valid-A indicator factors through the quotient ℤ/n → ℤ/(n/2) (mod antipodal); count downstairs then lift.
128. Stratify by the number of antipodal pairs in A; per-stratum the e_1 is a sum of `j` antipodal-pair values (which are 0!) plus singletons ⟹ e_1 = sum of singletons only ⟹ count = #singleton-configs, explicit.
129. The antipodal balance is an `F_2`-linear condition on the support indicator; I_∞ = q-independent count of an affine F_2-variety image, computed by Gauss elimination over F_2.
130. Vanishing-sum classification (Conway–Jones for 2-power = antipodal only) ⟹ the constraint solutions are an EXPLICIT finite union; enumerate and bound the union size by `O(n)`.

### R-γ. Container / spread / fractional (131–142) [from F47,F53]
131. Build a container family for the e_2=0 hypergraph using the EXACT antipodal structure as the "fingerprint"; show #containers = O(1) ⟹ I_∞ = O(n).
132. Spread-lemma (Park–Pham/Frankston): the antipodal configs are p-spread with small p ⟹ few of them.
133. Balanced-supersaturation for the antipodal-constraint hypergraph ⟹ container bound.
134. Hypergraph regularity (the EXACT version, no genericity) decomposes valid-A into O(1) structured pieces.
135. The constraint set has a bounded "VC-like" antipodal shattering dimension (2-power-specific) ⟹ Sauer count.
136. Fractional-relaxation LP: the natural LP for #valid A has integrality gap 1 here (rigid structure) ⟹ count = LP value, computed.
137. Entropy (Shearer over the antipodal pairs, which are independent) ⟹ exact log-count = Σ per-pair entropies.
138. Bukh-style "sums of dilates" container specialized to the dyadic dilate lattice.
139. The antipodal pairs partition the ground set; valid A = a "transversal-design"-respecting choice ⟹ design-theory count.
140. Kruskal–Katona on the antipodal-pair shadow bounds the number of e_2=0 sets of given size.
141. Local-central-limit for the e_1 of a random antipodal-balanced A ⟹ the value-set size = (range)/(lattice spacing) = O(n).
142. Janson/Suen correlation inequalities to pin the count from the antipodal independence.

### R-δ. Generating function / transfer matrix (143–154) [from H63–H69]
143. Write the EXACT bivariate GF `F(x,t)=Σ_{S} x^{e_1(S)} t^{|S|}·[e_2(S)=0]` as a constant-term over the n/2-pair lattice; extract `[x^γ]` count.
144. The GF is D-finite (holonomic) in n by the 2-power recursion; the singularity gives I_∞(δ)'s growth in closed form.
145. MacMahon Ω / partition-analysis to evaluate the constrained subset GF exactly.
146. Transfer-matrix along the antipodal-pair chain; I_∞(δ) = trace, growth = spectral radius (computed once).
147. Singularity analysis (Flajolet–Sedgewick) of the algebraic/Mahler GF ⟹ the `δ→capacity` growth exponent.
148. Creative telescoping (Zeilberger) ⟹ an explicit P-recurrence for I_∞(δ) ⟹ solve asymptotics.
149. The GF satisfies a Mahler functional equation (R-α #111); Mahler-asymptotics machinery (Dumas, Bell) ⟹ growth.
150. Lagrange inversion for the antipodal-tree branching (R-α #106) ⟹ closed product for the count.
151. Symmetric-function plethysm: `[e_2=0]` is a plethystic condition; evaluate via the character of the symmetric group.
152. The constrained subset count = a specialization of a Schur/Hall–Littlewood polynomial at roots of unity; use principal specialization.
153. Cycle-index / Pólya enumeration over the 2-group action ⟹ exact count.
154. q-analog: the count is a q→ root-of-unity evaluation of a Gaussian binomial product (cyclic sieving!) — the **cyclic sieving phenomenon** may give I_∞ in closed form.

### R-ε. Integrable / log-gas / statistical-mechanics (155–166) [from M94,M95,M96]
155. The e_1-distribution over antipodal-balanced A is a determinantal point process (free-fermion); I_∞ = #atoms via the correlation kernel.
156. Coulomb-gas on the unit circle (Dyson): the e_1 values are a log-gas equilibrium; the value-set size = (potential support)/(spacing), explicit.
157. Six-vertex / free-fermion partition function whose ground states = e_2=0 sets; transfer-matrix exact.
158. The constraint = a dimer/matching model on the antipodal-pair graph; Kasteleyn determinant = the count.
159. Ising on ℤ/n at the antipodal coupling; I_∞ = ground-state degeneracy, computed via the exact Onsager solution.
160. Tutte/Potts partition function specialization counts the antipodal configurations.
161. Bethe-ansatz exact spectrum of the symmetric-function "Hamiltonian" ⟹ count = #Bethe roots.
162. Yang–Baxter / R-matrix for the cyclotomic constraint ⟹ commuting transfer matrices ⟹ exact diagonalization.
163. Conformal-field-theory / Coulomb-gas scaling exponent gives the `δ→capacity` growth law.
164. The macroscopic limit shape of antipodal-balanced A (variational principle) ⟹ the count's exponential rate.
165. Tracy–Widom / edge-scaling for the extreme e_1 value ⟹ the value-set range ⟹ count.
166. Replica / cavity (rigorous, since the structure is a tree) for the count.

### R-ζ. Uniformity / transfer / SOS (167–178) [from K84,L87]
167. Ax–Grothendieck / Lefschetz transfer of a CHAR-0 count bound (proven for ℂ) DOWN to F_q via q-independence — make the q-independence a formal model-completeness statement so the ℂ-bound transfers.
168. The q-independence IS a definability/uniformity statement; prove I_∞ is a constructible function of n with O(1) "components" ⟹ polynomial count (constructibility over the cyclotomic base, NOT o-minimal — use étale/Grothendieck constructibility).
169. A degree-`O(1)` SOS/Positivstellensatz certificate that #γ ≤ Cn, where the moment matrix uses the EXACT antipodal energies (not the generic spectral gap), dodging the GP wall.
170. Polynomial-method (Guth–Katz partitioning) on the e_1-value point set to bound incidences without character sums.
171. A "rigidity from exact structure" argument: the antipodal constraint forces the γ-locus to be a bounded-degree variety whose ℂ-points (and hence F_q points, q-indep) number O(n).
172. Pila–Wilkie REPLACED by a cyclotomic-specific counting: the γ are algebraic of bounded height/degree ⟹ a Bombieri–Pila determinant bound counts them.
173. Effective Łojasiewicz / quantifier elimination over ℚ(ζ_n) gives an explicit polynomial bound on #components of the γ-locus.
174. The constructible-function pushforward (Sym^w μ_n → γ-line) has fibers of bounded Euler characteristic ⟹ image size O(n) (motivic, but the COUNT is the q-indep Euler char).
175. Model-theoretic "uniform finiteness" (the theory of (ℚ(ζ_n))_n is tame in the right sense) ⟹ I_∞(δ) uniformly bounded by a definable function — pin that function.
176. A direct "exact-energy ⟹ exact-count" lemma: prove the energy-to-count inequality is TIGHT (no √-loss) precisely for antipodally-rigid sets, converting the proven exact char-0 energy into the count.
177. Lefschetz fixed-point / trace formula for the ×2 map computing I_∞ as a Lefschetz number (q-independent topological count).
178. Constructibility + the proven SATURATION (n-independence) ⟹ I_∞(δ) = lim is a single algebraic number per δ; compute it as the degree of an explicit 0-dimensional scheme.

### R-η. New hybrids born from the essays (179–200) — reserved
179–200. [To be filled from the per-approach essays: the best cross-pollinations, e.g. "transfer-matrix (R-α)
+ cyclic-sieving (R-δ #154) closed form", "determinantal log-gas (R-ε #155) + constructibility (R-ζ #168)",
"Mann antipodal F_2-linear (R-β #129) + container (R-γ #131)", "Mahler-functional-equation (R-α #111) +
singularity analysis (R-δ #147)". These are the synthesis targets the essays will produce.]

---
**Status:** Round 1 (100) written + shot down (≈70 die: GP/J/VAC/INC/NA/∞/SUP). Round 2 (≈78 concrete +
22 reserved) written to AVOID those modes — all q-independent, count-targeting, prize-scale, exact-structure,
sub-exponential. Next: per-approach essays → detailed attack list → subagent assault.
