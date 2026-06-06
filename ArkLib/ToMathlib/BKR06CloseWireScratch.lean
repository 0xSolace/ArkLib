import ArkLib.Data.CodingTheory.ListDecoding.Bounds
import ArkLib.ToMathlib.BKR06Close

open CodingTheory BKR06Close

/-- Verification: the prime-power instantiation lemma `exists_primePow_seq_of_body`
discharges the bare external `Prop` `rs_lambda_superpoly_extension_bkr06` modulo the
per-instance family residual `hbody` (BKR06 Lemma 3.5 pigeonhole construction,
indexed by the concrete witness sequence `bkr06PrimePowSeq`).  This confirms the
witness sequence has the exact shape the bare statement demands. -/
example
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    -- the still-open per-instance family residual, indexed by `bkr06PrimePowSeq`
    (hbody : ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = bkr06PrimePowSeq i → Fintype.card ι = bkr06PrimePowSeq i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := bkr06PrimePowSeq i
            let k : ℕ := Nat.floor ((q : ℝ) ^ α)
            let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
            let C := ReedSolomon.code domain k
            ((ListDecodable.closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.log q)) :
    rs_lambda_superpoly_extension_bkr06 α β hα hαβ hβ := by
  unfold rs_lambda_superpoly_extension_bkr06
  exact exists_primePow_seq_of_body hbody
