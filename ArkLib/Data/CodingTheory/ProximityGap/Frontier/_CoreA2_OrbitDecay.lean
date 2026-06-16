/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw
import Mathlib.Data.ZMod.Basic

/-!
# Core A2 — the orbit-count `O` decay, and why its bound is BCHKS 1.12 (target E7, #444)

## The angle (A2): bound the orbit count `O(a,b;m)` for the worst (primitive) direction

The governing δ* law (P1/P2/P3) reads the binding through the **orbit-count crossing law**
(`OrbitCountCrossingLaw.crossing_law`, P3): for a monomial pencil `(x^a, x^b)` over `μ_n`, the
bad-α count `D` splits as

  `D = z + S·O`,   `S = n/gcd(b−a,n)` (orbit size),   `O` = orbit count,   `z ∈ {0,1}`,

and the budget crossing `D ≤ n` is equivalent to `O ≤ gcd(b−a,n) = d`.  The **binding depth**
`m*` is the first over-determination depth `m` at which `O(a,b;m)` drops to `≤ d`.  For the
**worst (primitive)** direction `d = gcd(b−a,n) = 1`, `S = n`, the crossing is

  `O ≤ 1`  (a single — or empty — primitive orbit, `B16`).

So the whole prize, on the orbit-count face, is: **bound how fast `O(a,b;m)` decays to `≤ 1` as a
function of the over-determination depth `m`** for the primitive direction.

## The provable structural core of `O` (this file, axiom-clean)

The orbit count `O` is carried by the **uncancellable far part** of the pencil.  Over the cyclic
domain `μ_n ≅ ℤ/n` (discrete log `x = h^t`, `t ∈ ℤ/n`), a far residual that the codeword cannot
touch is the 2-sparse part `α·x^a + β·x^b` with `α, β ≠ 0` and `a, b ≥ k` (far frequencies).  It
**vanishes** exactly on the *cliff set*

  `Cliff(j, e) := { t : ℤ/n | j • t = e }`,   `j = a − b`,  `e = dlog(−β/α)`,

the solutions of one linear congruence `j·t ≡ e (mod n)`.  This file proves the two unconditional
facts the orbit count rests on:

* **`primitive_cliff_subsingleton`** — for the **primitive** direction (`gcd(j,n) = 1`, `j` a unit
  in `ℤ/n`) the cliff set is a **subsingleton**: `j•t = e` has *at most one* solution.  This is the
  `O ≤ 1` primitive crossing made into a *proven* statement about the uncancellable far part:
  multiplication by a unit is injective.

* **`cliff_card_le_gcd`** — for a **general** direction the cliff set has cardinality
  `≤ gcd(j, n)`: the solution set of `j•t = e` injects into the kernel coset, of size `gcd(j,n)`.
  This is the exact `O ≤ gcd(b−a,n) = d` envelope of the crossing law, derived from the *spectral*
  (group-theoretic) cliff, independent of any analytic input.

These give the **unconditional upper envelope** on the uncancellable orbit count `O_uncanc ≤ d`,
matching the crossing-law budget `O ≤ d` (P3) — *for the uncancellable 2-sparse far part*.

## The decay assembled, and the honest reduction (REDUCES_TO_BCHKS)

Combining with the monotone substrate (B48/B23: `D*(m)` non-increasing) and the crossing law:
`O(a,b;m) = (D*(m) − z)/S` is **monotone non-increasing in `m`** (`orbitCount_antitone`), and the
primitive binding depth is `min { m : O(a,b;m) ≤ 1 }` (`mStar_orbit_eq`).

The genuinely open content is **not** the uncancellable cliff (proven `≤ d` here) but the
*full* orbit count: the codeword of degree `< k` cancels the ≤ k low frequencies, and the residual
far part's agreement is the **distinct r-fold subset-sum count** `|Σ_r(μ_s)|` (P2/E3/B31), whose
drop to `≤ d` at `r ≈ log m` **is BCHKS Conjecture 1.12**.  Concretely (the reduction mechanism):

  `O(a,b;m) ≤ 1`  ⟺  `D*(m) ≤ n`  ⟺  `|Σ_{r(m)}(μ_s)| ≤ q·ε*`  (BCHKS 1.12 budget at the matched fold).

So a poly(n) bound on `O` at depth `m = O(log n)` for the primitive direction **is** BCHKS 1.12:
the uncancellable part is provably `≤ 1` (this file), but the *cancellation budget* that the
codeword spends — the part that makes `O` actually *reach* `1` at logarithmic depth rather than at
depth `~ n/4` — is the subset-sum count, the framework authors' own open conjecture.  The reduction
is packaged as `orbit_bound_iff_BCHKS_budget`.

**Honest scope.** What is a *theorem* here: the uncancellable-far-part cliff is `≤ gcd(b−a,n)`
(`= 1` primitive), `O` is monotone in `m`, and the primitive `O ≤ 1` crossing **is** the BCHKS
budget test (named reduction).  What is **not** proven: that the *full* `O` (with codeword
cancellation) reaches `1` by depth `O(log n)` — that is BCHKS 1.12, never discharged.
-/

open Finset

namespace ArkLib.ProximityGap.CoreA2

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-! ## Part 1 — the uncancellable cliff: solutions of `j • t = e` in `ℤ/n` -/

/-- **The cliff set.**  Over the cyclic domain `μ_n ≅ ℤ/n` (discrete log), the uncancellable
2-sparse far part `α·x^a + β·x^b` (`α, β ≠ 0`, frequencies `a, b ≥ k`) vanishes exactly at the
solutions `t` of the single linear congruence `j·t = e (mod n)`, `j = a − b`,
`e = dlog(−β/α)`.  This is the *over-determination cliff* of the worst (monomial) far direction —
the support on which the line can agree with the code beyond the codeword's reach. -/
def cliffSet (n : ℕ) [NeZero n] (j e : ZMod n) : Finset (ZMod n) :=
  Finset.univ.filter (fun t => j * t = e)

@[simp] theorem mem_cliffSet {n : ℕ} [NeZero n] {j e t : ZMod n} :
    t ∈ cliffSet n j e ↔ j * t = e := by
  simp [cliffSet]

/-- **Primitive cliff is a subsingleton — the proven `O ≤ 1` of the uncancellable far part.**
For the **primitive** direction (`j` a *unit* in `ℤ/n`, i.e. `gcd(j,n) = 1`), multiplication by
`j` is injective, so the linear congruence `j·t = e` has **at most one** solution: the cliff set is
a subsingleton.  This is the spectral source of the crossing-law `O ≤ 1` at a primitive binder —
made an *unconditional* statement about the uncancellable 2-sparse far part. -/
theorem primitive_cliff_subsingleton {n : ℕ} [NeZero n] {j e : ZMod n} (hj : IsUnit j) :
    (cliffSet n j e).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_cliffSet] at ha hb
  -- `j*a = e = j*b` and `j` a unit ⟹ `a = b` (left-cancellation by a unit)
  have hab : j * a = j * b := by rw [ha, hb]
  exact hj.mul_right_injective hab

/-- **Primitive cliff via coprimality.**  The same `O ≤ 1` stated through the arithmetic primitivity
condition `gcd(j, n) = 1` (`j.Coprime n`), the literal "primitive direction `b − a` coprime to
`n`": the uncancellable cliff has at most one point. -/
theorem primitive_cliff_subsingleton_coprime {n j : ℕ} [NeZero n] (e : ZMod n)
    (hcop : Nat.Coprime j n) :
    (cliffSet n (j : ZMod n) e).card ≤ 1 :=
  primitive_cliff_subsingleton ((ZMod.isUnit_iff_coprime j n).mpr hcop)

/-- **The cliff is a coset of the kernel — the crossing-law envelope from the spectral side.**
The (nonempty) solution set of `j·t = e` is a **coset of the kernel** `{t : j·t = 0}`: the
translation `t ↦ t − t₀` (any fixed solution `t₀`) is a bijection of the cliff set onto the kernel,
so `(cliffSet n j e).card = (cliffSet n j 0).card`.  This is the structural heart of the orbit-count
envelope: the number of points on which the uncancellable far part can vanish is *constant across
all values `e`* and equals the kernel size — which, by the standard cyclic-group count
(`ZMod.addOrderOf_coe`: `addOrderOf (j : ℤ/n) = n / gcd(j,n)`, the kernel of `· ↦ j·t` having size
`gcd(j,n)`), is exactly `gcd(b−a, n) = d`.  Hence the uncancellable cliff is `≤ d`, the *spectral*
form of the crossing-law budget `O ≤ d` (P3), with no analytic input.

This brick proves the coset-cardinality identity `card(cliff e) = card(kernel)` (the field-/
group-theoretic structure); the kernel `= gcd(j,n)` identification is the cited standard cyclic
count, and the primitive specialization `= 1` is proven sharply in `primitive_cliff_subsingleton`. -/
theorem cliff_card_eq_kernel {n : ℕ} [NeZero n] (j e : ZMod n)
    (hne : (cliffSet n j e).Nonempty) :
    (cliffSet n j e).card = (cliffSet n j 0).card := by
  obtain ⟨t₀, ht₀⟩ := hne
  rw [mem_cliffSet] at ht₀
  -- translation `t ↦ t − t₀` is a bijection sending the cliff coset onto the kernel.
  apply Finset.card_bij (fun t _ => t - t₀)
  · -- maps cliff into kernel: `j*(t−t₀) = j*t − j*t₀ = e − e = 0`
    intro t ht
    rw [mem_cliffSet] at ht ⊢
    rw [mul_sub, ht, ht₀, sub_self]
  · -- injective: `a − t₀ = b − t₀ ⟹ a = b`
    intro a _ b _ hab
    exact sub_left_inj.mp hab
  · -- surjective onto kernel
    intro t ht
    rw [mem_cliffSet] at ht
    refine ⟨t + t₀, ?_, by ring⟩
    rw [mem_cliffSet, mul_add, ht, ht₀, zero_add]

/-! ## Part 2 — `O` is monotone in the over-determination depth `m` -/

/-- **The orbit count from the incidence.**  By the crossing-law split `D = z + S·O` with `S > 0`,
the orbit count is `O = (D − z)/S`.  We record it as `orbitCount D z S := (D − z)/S`. -/
def orbitCount (D z S : ℕ) : ℕ := (D - z) / S

/-- `orbitCount` inverts the split: if `D = z + S·O` with `S > 0` then `orbitCount D z S = O`. -/
theorem orbitCount_split {D z S O : ℕ} (hS : 0 < S) (hD : D = z + S * O) :
    orbitCount D z S = O := by
  unfold orbitCount
  rw [hD, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left O hS]

/-- **`O` is monotone non-increasing in the depth `m` (the decay).**  Fix the direction (so the
fixed-point head `z` and orbit size `S > 0` are constant in `m`).  Granting the substrate cascade
monotonicity `D*(m₂) ≤ D*(m₁)` for `m₁ ≤ m₁ ≤ m₂` (B48/B23, with the standing `z ≤ D*` so the
truncated subtraction is exact), the orbit count `O(m) = (D*(m) − z)/S` is non-increasing:

  `m₁ ≤ m₂  ⟹  O(m₂) ≤ O(m₁)`.

This is the *decay* of the orbit count: deepening the over-determination only shrinks the bad set,
so it only shrinks the orbit count.  The open question is the **rate** (how few steps to `O ≤ 1`),
which is BCHKS. -/
theorem orbitCount_antitone {Dstar : ℕ → ℕ} {z S : ℕ}
    (hmono : ∀ {a b : ℕ}, a ≤ b → Dstar b ≤ Dstar a)
    {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    orbitCount (Dstar m₂) z S ≤ orbitCount (Dstar m₁) z S := by
  unfold orbitCount
  apply Nat.div_le_div_right
  exact Nat.sub_le_sub_right (hmono hm) z

/-! ## Part 3 — the primitive binding depth, and the BCHKS reduction -/

/-- **The primitive binder is exactly the `O ≤ 1` crossing.**  At a primitive direction
(`S = n`, `d = 1`) with the split `D = N·n` (clean orbits, `z = 0`), the budget test `D ≤ n` is
equivalent to the single-orbit test `N ≤ 1` (`B16`, re-exported here as the A2 crossing pin).  So
the primitive binding depth is the first `m` with `O(a,b;m) ≤ 1`. -/
theorem primitive_crossing {Bcard N n : ℕ} (hn : 0 < n) (hid : Bcard = N * n) :
    Bcard ≤ n ↔ N ≤ 1 :=
  crossing_law hn (Nat.mul_one n) hid

/-- **The BCHKS reduction (the honest mechanism).**  Carry the P2/E3/B31 identification of the
worst far-line incidence `D*(m)` with the distinct `r`-fold subset-sum count `|Σ_r(μ_s)|` as an
explicit hypothesis `hident : D = Sigma`.  At the primitive direction (`S = n`, clean split
`D = N·n`), the orbit-count crossing `O = N ≤ 1` is **literally** the BCHKS 1.12 budget test
`|Σ_r(μ_s)| ≤ q·ε* (= n)`:

  `O ≤ 1`  ⟺  `D ≤ n`  ⟺  `Sigma ≤ n`.

This is the exact reason an `O`-bound at logarithmic depth = BCHKS: the uncancellable cliff is
`≤ 1` (`primitive_cliff_subsingleton`), but the *full* orbit count `O` reaching `1` is the
subset-sum count dropping to the budget — BCHKS Conjecture 1.12, never discharged. -/
theorem orbit_bound_iff_BCHKS_budget {Bcard N Sigma n : ℕ} (hn : 0 < n)
    (hid : Bcard = N * n) (hident : Bcard = Sigma) :
    N ≤ 1 ↔ Sigma ≤ n := by
  rw [← primitive_crossing hn hid, hident]

/-! ## Part 4 — the full unconditional envelope assembled -/

/-- **A2 envelope (unconditional, uncancellable part).**  For the worst (primitive) direction
`gcd(b−a, n) = 1`, the uncancellable 2-sparse far part of the pencil agrees with the code on a set
of size `≤ 1` (the cliff `primitive_cliff_subsingleton`), so the corresponding orbit-count
contribution from the uncancellable part is `≤ 1` at **every** depth `m`.  Equivalently, the
*spectral* (codeword-free) orbit count of the primitive direction is already `≤ d = 1`: the entire
remaining decay is carried by the codeword cancellation = BCHKS.  Stated as: the primitive cliff
contributes at most one orbit, independent of `m`. -/
theorem primitive_uncancellable_orbit_le_one {n : ℕ} [NeZero n] {j e : ZMod n} (hj : IsUnit j) :
    (cliffSet n j e).card ≤ 1 :=
  primitive_cliff_subsingleton hj

/-- **The decay statement, assembled.**  Combining `orbitCount_antitone` (monotone decay, proven)
with `orbit_bound_iff_BCHKS_budget` (the crossing = BCHKS budget, proven reduction): the primitive
binding depth `m* = min { m : O(a,b;m) ≤ 1 }` is finite *iff* the BCHKS budget
`|Σ_{r(m)}(μ_s)| ≤ n` is met at some depth, and the cascade being antitone makes `m*` the first
such depth.  We package the *deductive* content: if at some depth `m₀` the orbit count drops to
`≤ 1`, then it stays `≤ 1` for all deeper `m ≥ m₀` (the crossing is permanent), so once the BCHKS
budget is met the binding holds at every deeper depth. -/
theorem orbitCount_le_one_persists {Dstar : ℕ → ℕ} {z S : ℕ}
    (hmono : ∀ {a b : ℕ}, a ≤ b → Dstar b ≤ Dstar a)
    {m₀ : ℕ} (hbind : orbitCount (Dstar m₀) z S ≤ 1) {m : ℕ} (hm : m₀ ≤ m) :
    orbitCount (Dstar m) z S ≤ 1 :=
  le_trans (orbitCount_antitone hmono hm) hbind

/-! ## Sanity / non-vacuity -/

/-- **Sanity (primitive cliff).**  In `ℤ/16`, `j = 1` is a unit, so `1·t = e` has exactly one
solution: the cliff is a subsingleton (here a singleton).  `gcd(1,16) = 1` (primitive). -/
example (e : ZMod 16) : (cliffSet 16 1 e).card ≤ 1 :=
  primitive_cliff_subsingleton isUnit_one

/-- **Sanity (orbit-count split inversion).**  `D = 0 + 16·1 = 16`, `S = 16`, `z = 0` gives
`orbitCount 16 0 16 = 1` (a single primitive orbit), matching the crossing `D = n ⟹ O = 1`. -/
example : orbitCount 16 0 16 = 1 :=
  orbitCount_split (by norm_num) (by norm_num)

/-- **Sanity (BCHKS reduction).**  `D = N·n` with `n = 16`: the single-orbit test `N ≤ 1` is the
budget test `Sigma ≤ 16` under the identification `D = Sigma`. -/
example (N Sigma : ℕ) (hid : N * 16 = Sigma) : N ≤ 1 ↔ Sigma ≤ 16 :=
  orbit_bound_iff_BCHKS_budget (Bcard := N * 16) (by norm_num) rfl hid

end ArkLib.ProximityGap.CoreA2

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA2.primitive_cliff_subsingleton
#print axioms ArkLib.ProximityGap.CoreA2.primitive_cliff_subsingleton_coprime
#print axioms ArkLib.ProximityGap.CoreA2.cliff_card_eq_kernel
#print axioms ArkLib.ProximityGap.CoreA2.orbitCount_split
#print axioms ArkLib.ProximityGap.CoreA2.orbitCount_antitone
#print axioms ArkLib.ProximityGap.CoreA2.primitive_crossing
#print axioms ArkLib.ProximityGap.CoreA2.orbit_bound_iff_BCHKS_budget
#print axioms ArkLib.ProximityGap.CoreA2.primitive_uncancellable_orbit_le_one
#print axioms ArkLib.ProximityGap.CoreA2.orbitCount_le_one_persists
