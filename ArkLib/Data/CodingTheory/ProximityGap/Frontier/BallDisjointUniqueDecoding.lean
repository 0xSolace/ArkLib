/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NubsCarson
-/
import ArkLib.Data.CodingTheory.ListDecodability

/-! # Disjoint radius-`r` balls below half the distance (unique-decoding geometry)

The geometric fact underpinning the lower-window half of the δ* closed form
(`DISPROOF_LOG` O173/O182): below the unique-decoding radius — when `2r < d` for `d` the
Hamming distance between two codewords — their radius-`r` Hamming balls are disjoint, so no
received word is `r`-close to both. Consequently the second-moment cross term
`Σ_d A_d · I_∩(d)` over codeword pairs is empty for `δ < (1−ρ)/2` (where `2⌊δn⌋ < d_min`), so
`worst = average` and the closed form `δ* = H_q⁻¹(1−ρ−log_q(1/ε*)/n)` holds *unconditionally*
in the lower window.

Self-contained: a triangle-inequality argument. No MDS machinery is needed — the distance is
taken as a hypothesis, which any code satisfies for distinct codewords with `d := d_min`. -/

open Classical

namespace ListDecodable

variable {ι : Type*} [Fintype ι] {F : Type*}

/-- If two centres are more than `2r` apart in Hamming distance, their radius-`r` Hamming balls
are disjoint. (Triangle inequality — the unique-decoding region.) -/
theorem hammingBall_disjoint_of_two_mul_lt_dist
    {c c' : ι → F} {r : ℕ} (h : 2 * r < hammingDist c c') :
    Disjoint (hammingBall c r) (hammingBall c' r) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hammingBall, Set.mem_setOf_eq] at hx hx'
  have hx'' : hammingDist x c' ≤ r := by rw [hammingDist_comm]; exact hx'
  have hle : hammingDist c c' ≤ 2 * r :=
    calc hammingDist c c' ≤ hammingDist c x + hammingDist x c' := hammingDist_triangle c x c'
      _ ≤ r + r := Nat.add_le_add hx hx''
      _ = 2 * r := (two_mul r).symm
  omega

/-- Below the unique-decoding radius, no received word `y` is `r`-close to two codewords that
are more than `2r` apart: the radius-`r` ball intersection (the second-moment cross term over
codeword pairs) is empty. -/
theorem not_closeCodewords_two_of_two_mul_lt_dist
    {C : Code ι F} {y c c' : ι → F} {r : ℕ}
    (hc : c ∈ closeCodewords C y r) (hc' : c' ∈ closeCodewords C y r)
    (h : 2 * r < hammingDist c c') : False := by
  obtain ⟨_, hcy⟩ := hc
  obtain ⟨_, hc'y⟩ := hc'
  simp only [hammingBall, Set.mem_setOf_eq] at hcy hc'y
  have hcy' : hammingDist c y ≤ r := by rw [hammingDist_comm]; exact hcy
  have hle : hammingDist c c' ≤ 2 * r :=
    calc hammingDist c c' ≤ hammingDist c y + hammingDist y c' := hammingDist_triangle c y c'
      _ ≤ r + r := Nat.add_le_add hcy' hc'y
      _ = 2 * r := (two_mul r).symm
  omega

end ListDecodable
