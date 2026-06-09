/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKeystone

/-!
# The composite round-by-round *knowledge* state function — `Verifier.KnowledgeStateFunction.append`

This file constructs the witness-threaded analogue of the proven `Verifier.StateFunction.append`
(`Append.lean`): the composite round-by-round **knowledge** state function for the appended verifier
`V₁.append V₂`, built against the proven composite round-by-round extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. With it the residual `kSF` of
`Verifier.append_rbrKnowledgeSoundness_keystone` (`AppendRbrKeystone.lean`) is discharged.

The `toFun` carrier mirrors `StateFunction.append`: on a phase-1 round (`roundIdx.val ≤ m`) it is the
inner knowledge state function `kSF₁` on the transcript's phase-1 truncation; on a phase-2 round it is
`kSF₂` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. The only new
ingredient relative to `StateFunction.append` is the intermediate-witness leg: the appended extractor's
combined `WitMid` carrier `Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` projects to `WitMid₁`
on phase-1 rounds and `WitMid₂` on phase-2 rounds (`appendWitMid_le` / `appendWitMid_gt`), and the
state function casts the supplied combined witness into the appropriate leg before feeding it to
`kSF₁` / `kSF₂`.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Phase-1 projection of the composite `WitMid` carrier.** For a round index `roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₁`'s leg at the
re-indexed `⟨roundIdx, _⟩ : Fin (m+1)`. -/
theorem appendWitMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₁ ⟨roundIdx, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n)) = Fin.castAdd n ⟨roundIdx, by omega⟩ from by
    ext; simp]
  rw [Fin.append_left]

/-- **Phase-2 projection of the composite `WitMid` carrier.** For a round index `¬ roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₂`'s leg at the
re-indexed `⟨roundIdx - m, _⟩ : Fin (n+1)`. -/
theorem appendWitMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : ¬ roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₂ ⟨roundIdx - m, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n))
        = Fin.natAdd (m+1) ⟨roundIdx-(m+1), by omega⟩ from by ext; simp; omega]
  rw [Fin.append_right]; show Fin.tail WitMid₂ _ = _; unfold Fin.tail; congr 1
  ext; simp only [Fin.val_succ]; omega

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-1 projection of the composite `extractMid`.** For a round index `idx < m` (entirely in
phase 1), the appended extractor's `extractMid` defers — heterogeneously, up to the witness/transcript
type casts — to `E₁.extractMid ⟨idx,hi⟩` on the transcript's phase-1 truncation. -/
theorem appendExtractMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) < m) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.Transcript (⟨idx, hi⟩ : Fin m).succ) (htrf : HEq tr.fst trf)
    (hin : WitMid₁ (⟨idx, hi⟩ : Fin m).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractMid ⟨idx, hi⟩ stmt₁ trf hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_pos hi]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) ?_
  refine dcongr_heq (HEq.trans (cast_heq _ _) hheq) (fun _ _ _ => rfl)
    (fun _ _ => heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf)))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 (interior) projection of the composite `extractMid`.** For a round index `idx > m`
(strictly inside phase 2), the appended extractor's `extractMid` defers — heterogeneously — to
`E₂.extractMid ⟨idx-m,_⟩` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. -/
theorem appendExtractMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : m < (idx:ℕ)) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩ (verify stmt₁ trf) trs hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_neg (show ¬ (idx:ℕ) = m from by omega)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (HEq.trans (HEq.trans (cast_heq _ _) (cast_heq _ _))
      (HEq.trans (cast_heq _ _) hheq)) (fun _ _ _ => rfl) (fun _ _ => ?_)
  refine heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩) ?_))
    (HEq.trans (cast_heq _ _) htrs))
  exact congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Crossing projection of the composite `extractMid`.** At the seam round `idx = m`, the appended
extractor peels one phase-2 round with `E₂.extractMid 0` (landing in `Wit₂` via `E₂.eqIn`) and crosses
into phase 1 with `E₁.extractOut` on the `verify`-fed intermediate statement. -/
theorem appendExtractMid_cross {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) = m) (hn : 0 < n) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨0, hn⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractOut stmt₁ trf
          (cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_pos (show (idx:ℕ) = m from hi)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (a₁ := _) (a₂ := cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))
    ?hw (fun _ _ _ => rfl) (fun _ _ => ?hf)
  case hw =>
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine dcongr_heq (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (HEq.trans (cast_heq _ _) hheq))) (fun _ _ _ => rfl)
      (fun _ _ => heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨0, hn⟩)
        (congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf)))))
        (HEq.trans (cast_heq _ _) htrs)))
  case hf =>
    exact heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 projection of the composite `extractOut`.** For `n > 0` the appended protocol's final
round is interior to phase 2, so the appended extractor's `extractOut` defers — heterogeneously, up
to the witness type cast — to `E₂.extractOut` on the `verify`-fed intermediate statement and the
transcript's phase-2 tail. The `extractOut` analogue of `appendExtractMid_gt`. -/
theorem appendExtractOut_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hn : 0 < n) (stmt₁ : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (witOut : Wit₃)
    (h : ¬ ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) ≤ m) :
    HEq (cast (appendWitMid_gt h)
          ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
        (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) witOut) := by
  refine HEq.trans (cast_heq _ _) ?_
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  simp only [dif_neg (show ¬ n = 0 from by omega), id_eq]
  refine HEq.trans ?_ (HEq.refl (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr))
    (FullTranscript.snd tr) witOut))
  rw [eq_mpr_eq_cast]
  refine HEq.trans (cast_heq _ _) (cast_heq _ _)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a knowledge state function's `toFun`.** Two applications of a (raw)
round-by-round knowledge `toFun` family agree (as `Prop`s) when the round indices are equal and the
transcript and intermediate-witness arguments are heterogeneously equal. The protocol-independent
glue that lets the seam-transport HEq facts collapse into the `Prop`-level equalities consumed by
`kSF₁.toFun_next` / `kSF₂.toFun_next`. -/
theorem kToFun_congr {WitMid : Fin (n+1)→Type} {Stmt : Type}
    (f : (r : Fin (n+1)) → Stmt → pSpec₂.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (n+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₂.Transcript r₁} {t₂ : pSpec₂.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **`kToFun_congr` for the first (phase-1) protocol.** Same as `kToFun_congr` over `pSpec₁`. -/
theorem kToFun_congr₁ {WitMid : Fin (m+1)→Type} {Stmt : Type}
    (f : (r : Fin (m+1)) → Stmt → pSpec₁.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (m+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₁.Transcript r₁} {t₂ : pSpec₁.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The phase-1 transcript-truncation seam.** For a phase-1 round (`roundIdx < m`), concatenating a
phase-1 message `msg` and taking the appended-spec transcript's phase-1 truncation is heterogeneously
equal to first truncating and then concatenating the recast message. Mirrors the inline computation in
`StateFunction.append.toFun_next`. -/
theorem concat_fst_heq_phase1 {roundIdx : Fin (m + n)} (hlt : (roundIdx : ℕ) < m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx)
    (hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩) :
    HEq (Transcript.concat msg tr).fst
        (Transcript.concat (cast hmsgty msg)
          (by simpa [show (roundIdx : ℕ) ≤ m from le_of_lt hlt] using tr.fst :
            pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc)) := by
  have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
  apply Function.hfunext
  · congr 1; simp only [Fin.val_succ]; omega
  · intro a a' haa'
    have hav : a.val = a'.val := by
      have := Fin.heq_ext_iff (by simp only [Fin.val_succ]; omega) |>.mp haa'
      omega
    simp only [Transcript.concat, Transcript.fst]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_succ] at hav hav_lt ⊢
    rw [show min ((roundIdx : ℕ) + 1) m = (roundIdx : ℕ) + 1 from by omega] at hav_lt
    simp only [Fin.snoc]
    by_cases hlast : av = roundIdx
    · rw [dif_neg (show ¬ av < roundIdx from by omega),
          dif_neg (show ¬ (a' : ℕ) < roundIdx from by omega)]
      -- goal `cast (cast msg) ≍ cast (cast hmsgty msg)`; route both through `msg`.
      refine HEq.trans (b := msg) (HEq.trans (cast_heq _ _) (cast_heq _ _)) ?_
      exact HEq.symm (HEq.trans (cast_heq _ _) (cast_heq hmsgty msg))
    · have hlt' : av < roundIdx := by omega
      rw [dif_pos (show (a' : ℕ) < roundIdx from by omega),
          dif_pos (show av < roundIdx from hlt')]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      have hmincard : min (roundIdx : ℕ) m = (roundIdx : ℕ) := by omega
      refine HEq.trans ?_ (dcongr_heq (f₁ := Transcript.fst tr)
        (a₁ := (⟨av, by omega⟩ : Fin (min (roundIdx : ℕ) m)))
        (a₂ := (a'.castLT (show (a' : ℕ) < roundIdx from by omega)))
        (Fin.heq_ext_iff hmincard |>.mpr (by simpa using hav))
        (fun t₁ t₂ ht => by
          have hv : (t₁ : ℕ) = (t₂ : ℕ) := Fin.val_eq_val_of_heq ht
          show pSpec₁.Type _ = pSpec₁.Type _
          congr 1; ext; simpa using hv)
        (fun _ _ => HEq.symm (cast_heq _ _ :
          (by simpa [hcs] using tr.fst : pSpec₁.Transcript ⟨roundIdx, by omega⟩)
            ≍ Transcript.fst tr)))
      unfold Transcript.fst
      refine HEq.trans ?_ (cast_heq _ _).symm
      congr 1

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-1 prefix is invariant under a phase-2 concat.** For a phase-2 round (`m ≤ roundIdx`),
concatenating a phase-2 message `msg` onto the transcript leaves the phase-1 truncation `fst`
unchanged (heterogeneously). Mirrors the `hfstHeq` computation in `StateFunction.append.toFun_next`
(`Append.lean:1407–1430`). -/
theorem concat_fst_heq_phase2 {roundIdx : Fin (m + n)} (hge : m ≤ (roundIdx : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx) :
    HEq (Transcript.concat msg tr).fst tr.fst := by
  have hcard : min ((roundIdx : Fin (m + n)).succ : ℕ) m
      = min ((roundIdx : Fin (m + n)).castSucc : ℕ) m := by
    simp only [Fin.val_succ, Fin.val_castSucc]; omega
  apply Function.hfunext
  · congr 1
  · intro a a' haa'
    have hav : (a : ℕ) = (a' : ℕ) := by
      have := Fin.heq_ext_iff hcard |>.mp haa'; omega
    simp only [Transcript.concat, Transcript.fst]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_succ] at hav hav_lt ⊢
    rw [show min ((roundIdx : ℕ) + 1) m = m from by omega] at hav_lt
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans ?_ (cast_heq _ _).symm
    simp only [Fin.snoc]
    rw [dif_pos (show av < roundIdx from by omega)]
    refine HEq.trans (cast_heq _ _) ?_
    congr 1
    ext; simp only [Fin.val_castLT]; omega

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The phase-2 transcript-tail seam.** For a phase-2 round (`m ≤ roundIdx`), concatenating a
phase-2 message `msg` and taking the appended-spec transcript's phase-2 tail is heterogeneously
equal to first taking the tail and then concatenating the recast message. The `.snd` analogue of
`concat_fst_heq_phase1`; mirrors the inline computation in `StateFunction.append.toFun_next`
(`Append.lean:1544–1583`). -/
theorem concat_snd_heq_phase2 {roundIdx : Fin (m + n)} (hge : m ≤ (roundIdx : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx)
    (hmsgty₂ : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₂.Type ⟨(roundIdx : ℕ) - m, by omega⟩) :
    HEq (Transcript.concat msg tr).snd
        (Transcript.concat (cast hmsgty₂ msg)
          (by simpa using tr.snd :
            pSpec₂.Transcript (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).castSucc)) := by
  have hsndcard : ((roundIdx : ℕ) - m) + 1 = ((roundIdx : Fin (m + n)).succ : ℕ) - m := by
    simp only [Fin.val_succ]; omega
  symm
  apply Function.hfunext
  · congr 1
  · intro a a' haa'
    have haa : (a : ℕ) = (a' : ℕ) := by
      have := Fin.heq_ext_iff hsndcard |>.mp haa'; omega
    simp only [Transcript.concat]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_mk] at haa hav_lt ⊢
    -- the RHS `(concat msg tr).snd` always lands in the `else` branch (its index `> m`)
    rw [show (Transcript.concat msg tr).snd (⟨(a' : ℕ), a'.isLt⟩ : Fin _)
          = (Transcript.concat msg tr).snd a' from by congr]
    unfold Transcript.snd
    rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).succ ≤ m from by
          simp only [Fin.val_succ]; omega)]
    -- the LHS `Fin.snoc ((tr.snd cast)) msg₂`: split on whether `av` is the last position
    simp only [Fin.snoc]
    by_cases hlast : av = (roundIdx : ℕ) - m
    · rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
          dif_neg (show ¬ m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
      -- both sides are `msg` (the new message), up to casts
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans (cast_heq _ _) ?_
      exact HEq.trans (cast_heq _ _).symm (cast_heq _ _).symm
    · -- earlier position: both read the original `tr.snd` at the same underlying index
      have hlt2 : av < (roundIdx : ℕ) - m := by omega
      rw [dif_pos (show av < (roundIdx : ℕ) - m from hlt2)]
      rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).castSucc ≤ m from by
            simp only [Fin.val_castSucc]; omega)]
      rw [dif_pos (show m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1
      ext; simp only [Fin.val_castLT]; omega

/-- **Membership lifts to positive probability for a deterministic verifier.** If the first verifier
is `V₁ = pure ∘ verify` with a reachable initial state (`∃ s, s ∈ support init`), and the
intermediate statement/witness pair `(verify stmt₁ trFst, witOut)` lies in `rel₂`, then the
`Pr[(·, witOut) ∈ rel₂ | …] > 0` hypothesis of `kSF₁.toFun_full` is met: the deterministic run
outputs `verify stmt₁ trFst`, which witnesses the positive probability. The positive-probability dual
of `StateFunction.verify_not_mem_lang_of_toFun_full_neg`; shared by the crossing case of
`toFun_next` and by `toFun_full`. -/
theorem run_pos_of_mem_rel
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {rel₂ : Set (Stmt₂ × Wit₂)}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (stmt₁ : Stmt₁) (trFst : pSpec₁.FullTranscript) (witOut : Wit₂)
    (hMem : (verify stmt₁ trFst, witOut) ∈ rel₂) :
    Pr[fun stmtOut => (stmtOut, witOut) ∈ rel₂
      | OptionT.mk do (simulateQ impl (V₁.run stmt₁ trFst)).run' (← init)] > 0 := by
  rw [gt_iff_lt, probEvent_pos_iff]
  obtain ⟨s, hs⟩ := hInit
  refine ⟨verify stmt₁ trFst, ?_, hMem⟩
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt₁ trFst) = (pure (verify stmt₁ trFst) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt₁ trFst) ∈ _root_.support
    (StateT.run' (simulateQ impl (pure (some (verify stmt₁ trFst)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt₁ trFst) ∈ _root_.support
    (Prod.fst <$> (pure (some (verify stmt₁ trFst)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [map_pure]

/-- The sequential composition of two **knowledge** state functions, witness-threaded analogue of
`Verifier.StateFunction.append`. Built against the proven composite extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. -/
def KnowledgeStateFunction.append {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.append E₁ E₂ verify) where
  toFun := fun roundIdx stmt₁ tr witMid =>
    if h : roundIdx.val ≤ m then
      kSF₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using tr.fst)
        (cast (appendWitMid_le h) witMid)
    else
      kSF₂.toFun ⟨roundIdx - m, by omega⟩
        (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using tr.fst))
        (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid)
  toFun_empty := by
    intro stmtIn witMid
    -- At round `0`, `(0 : Fin (m+n+1)).val = 0 ≤ m`, so `toFun 0 = kSF₁.toFun ⟨0,_⟩ … (.fst) …`.
    have h0 : ((0 : Fin (m + n + 1)) : ℕ) ≤ m := by simp
    simp only [dif_pos h0]
    -- The witness-cast coherence: `cast (append.eqIn) witMid = cast E₁.eqIn (cast (appendWitMid_le …))`.
    have hwit : cast (Extractor.RoundByRound.append E₁ E₂ verify).eqIn witMid
        = cast E₁.eqIn (cast (appendWitMid_le h0) witMid) := by
      rw [cast_cast]
    rw [hwit]
    -- Now reduce to `kSF₁.toFun_empty`, re-indexing `⟨0,_⟩ : Fin (m+1)` as `0` and `.fst = default`.
    refine Iff.trans (kSF₁.toFun_empty stmtIn (cast (appendWitMid_le h0) witMid)) (Iff.of_eq ?_)
    congr 1
    funext i; exact i.elim0
  toFun_next := by
    intro roundIdx hDir stmt₁ tr msg witMid hPrev
    by_cases hlt : (roundIdx : ℕ) < m
    · -- Phase 1: both `roundIdx.succ` and `roundIdx.castSucc` land in the `≤ m` (kSF₁) branch.
      have hsucc : (roundIdx : ℕ) + 1 ≤ m := hlt
      have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hsucc] at hPrev
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hcs]
      -- The phase-1 direction.
      have hDir₁ : pSpec₁.dir ⟨roundIdx, hlt⟩ = .P_to_V := by
        rw [← Fin.vappend_left_of_lt pSpec₁.dir pSpec₂.dir roundIdx hlt]; exact hDir
      have hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩
        rw [Fin.vappend_left_of_lt _ _ _ hlt]
      -- The phase-1 truncated transcript and witness.
      set trf : pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc :=
        (by simpa [hcs] using tr.fst) with htrf_def
      set wit₁ : WitMid₁ (⟨roundIdx, hlt⟩ : Fin m).succ :=
        cast (appendWitMid_le hsucc) witMid with hwit₁_def
      -- The shared transcript-truncation seam.
      have htrEq : HEq (Transcript.concat msg tr).fst (trf.concat (cast hmsgty msg)) :=
        concat_fst_heq_phase1 hlt tr msg hmsgty
      -- `hPrev` reshaped to `kSF₁.toFun (succ) stmt₁ (trf.concat (cast msg)) wit₁`.
      have hPrev₁ : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁
          (trf.concat (cast hmsgty msg)) wit₁ := by
        have e : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁ (trf.concat (cast hmsgty msg)) wit₁
            = kSF₁.toFun ⟨(roundIdx : ℕ) + 1, by omega⟩ stmt₁
              (by simpa [hsucc] using (Transcript.concat msg tr).fst)
              (cast (appendWitMid_le hsucc) witMid) :=
          kToFun_congr₁ kSF₁.toFun (Fin.ext (by simp [Fin.val_succ]))
            stmt₁ (htrEq.symm.trans (cast_heq _ _).symm) HEq.rfl
        rw [e]; exact hPrev
      -- Apply `kSF₁.toFun_next` and transport to the goal via `appendExtractMid_le`.
      have key := kSF₁.toFun_next ⟨roundIdx, hlt⟩ hDir₁ stmt₁ trf (cast hmsgty msg) wit₁ hPrev₁
      -- The goal's witness is `cast _ ((append…).extractMid …)`; `key`'s is
      -- `E₁.extractMid ⟨roundIdx,hlt⟩ stmt₁ (trf.concat (cast msg)) wit₁`. Identify via
      -- `appendExtractMid_le`, the transcripts via `htrf_def`/`htrEq`.
      have hExtEq : HEq (cast (appendWitMid_le hcs)
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
              (Transcript.concat msg tr) witMid))
          (E₁.extractMid ⟨roundIdx, hlt⟩ stmt₁ (trf.concat (cast hmsgty msg)) wit₁) :=
        (cast_heq _ _).trans (appendExtractMid_le E₁ E₂ verify roundIdx hlt stmt₁
          (Transcript.concat msg tr) witMid (trf.concat (cast hmsgty msg)) htrEq wit₁
          (cast_heq _ _).symm)
      -- Close the goal by transporting `key` across the index/transcript/witness coherences.
      refine Eq.mp ?_ key
      exact kToFun_congr₁ kSF₁.toFun
        (Fin.ext (by simp [Fin.val_castSucc]) :
          (⟨roundIdx, hlt⟩ : Fin m).castSucc = ⟨(roundIdx : ℕ), by omega⟩)
        stmt₁ ((cast_heq _ _).trans (cast_heq _ _).symm) hExtEq.symm
    · -- `roundIdx ≥ m`. Two sub-cases.
      --
      -- PHASE-2 INTERIOR (`roundIdx > m`): structurally identical to the phase-1 case above, with
      --   `kSF₂` / `appendExtractMid_gt` / `appendWitMid_gt` in place of the phase-1 versions, the
      --   statement `verify stmt₁ tr.fst` (invariant under the phase-2 concat — see the `.fst`
      --   invariance below), and the *second-segment* transcript seam: `(tr.concat msg).snd` is
      --   heterogeneously `(tr.snd).concat (cast msg)` (mirroring `StateFunction.append.toFun_next`,
      --   `Append.lean:1544–1583`). Both `dite` branches land in `kSF₂` (`dif_neg`), and
      --   `kSF₂.toFun_next ⟨roundIdx-m,_⟩` closes it via the same `kToFun_congr` / `Eq.mp` transport
      --   used in phase 1. (Fully scaffolded; the only missing brick is the `.snd` transcript-seam
      --   `HEq` lemma — the `.snd` analogue of the proven `concat_fst_heq_phase1` — whose `dite`
      --   bookkeeping over `Transcript.snd` is the entirety of the remaining work.)
      --
      -- CROSSING (`roundIdx = m`): the hypothesis is `kSF₂.toFun ⟨1,_⟩ (verify stmt₁ tr.fst)
      --   ((tr.concat msg).snd) witMid` (phase-2 index 1) and the goal is `kSF₁.toFun (Fin.last m)
      --   stmt₁ tr.fst (E₁.extractOut stmt₁ tr.fst (cast E₂.eqIn (E₂.extractMid 0 … witMid)))` (via
      --   `appendExtractMid_cross`). The chain is the DUAL of `StateFunction.append.toFun_next`'s
      --   crossing (which propagates *falsity* through the language): here we propagate *truth*:
      --     1. `kSF₂.toFun_next 0` turns the hypothesis into
      --        `kSF₂.toFun 0 (verify …) default (E₂.extractMid 0 … witMid)`;
      --     2. `kSF₂.toFun_empty` then gives `(verify stmt₁ tr.fst, cast E₂.eqIn (E₂.extractMid 0 …))
      --        ∈ rel₂`;
      --     3. since `V₁` is deterministic (`hVerify`), `V₁.run stmt₁ tr.fst = pure (verify …)`, so the
      --        `Pr[(·, wit₂) ∈ rel₂ | V₁.run …] > 0` hypothesis of `kSF₁.toFun_full` holds (the run
      --        deterministically outputs `verify stmt₁ tr.fst`);
      --     4. `kSF₁.toFun_full` then yields exactly the goal `kSF₁.toFun (last m) stmt₁ tr.fst
      --        (E₁.extractOut stmt₁ tr.fst wit₂)`.
      --   This sub-case is provable (it is NOT the `hBound` residual — that is a *probabilistic*
      --   per-round bound, a different obligation); the blocker is purely the `Pr > 0` plumbing from
      --   `hVerify` (the same deterministic-run collapse used in `toFun_full` below).
      rw [not_lt] at hlt
      -- `hPrev`'s index `roundIdx.succ.val = roundIdx + 1 > m` always lands in the `kSF₂` branch.
      have hnsucc : ¬ ((roundIdx : ℕ) + 1 ≤ m) := by omega
      simp only [Fin.val_succ, dif_neg hnsucc] at hPrev
      -- The phase-2 direction at this round.
      have hDir₂ : pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩ = .P_to_V := by
        rw [show pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩
              = (pSpec₁.dir ++ᵛ pSpec₂.dir) roundIdx
            from (Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)).symm]
        exact hDir
      -- The message transported into the second segment's type.
      have hmsgty₂ : (pSpec₁ ++ₚ pSpec₂).Type roundIdx
          = pSpec₂.Type ⟨(roundIdx : ℕ) - m, by omega⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = _
        rw [Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)]
      -- The phase-2 truncated transcript: `tr.snd` as a `castSucc`-indexed transcript.
      set trs : pSpec₂.Transcript (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).castSucc :=
        (by simpa using tr.snd) with htrs_def
      -- The phase-1 prefix as a genuine full transcript (`roundIdx ≥ m`, so the domain is all `m`).
      have hmin : min (roundIdx : ℕ) m = m := by omega
      set trFst : pSpec₁.FullTranscript := (by simpa [hmin] using tr.fst) with htrFst_def
      have htrFst_heq : (trFst : pSpec₁.FullTranscript) ≍ tr.fst := cast_heq _ _
      by_cases hcross : (roundIdx : ℕ) = m
      · -- CROSSING (`roundIdx = m`): goal's `roundIdx.castSucc.val = m ≤ m` lands in `kSF₁`.
        have hcs : (roundIdx : ℕ) ≤ m := by omega
        simp only [Fin.val_castSucc, dif_pos hcs]
        have hn1 : 0 < n := by have := (roundIdx : Fin (m + n)).isLt; omega
        -- (1) `hPrev` (at phase-2 index `roundIdx + 1 - m = 1`) reshaped to `kSF₂.toFun 0.succ
        --     (verify … trFst) (empty.concat msg₂) witMid₂`.
        have hmsgty0 : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₂.Type (⟨0, hn1⟩ : Fin n) := by
          rw [hmsgty₂]; congr 1; ext; simp only [Fin.val_mk]; omega
        set witMid₂ : WitMid₂ (⟨0, hn1⟩ : Fin n).succ :=
          cast (show WitMid₂ ⟨((roundIdx : Fin (m + n)).succ : ℕ) - m, by simp only [Fin.val_succ]; omega⟩
              = WitMid₂ (⟨0, hn1⟩ : Fin n).succ from by
                congr 1; ext; simp only [Fin.val_succ, Fin.val_mk]; omega)
            (cast (appendWitMid_gt (by simp only [Fin.val_succ]; omega :
              ¬ ((roundIdx : Fin (m + n)).succ : ℕ) ≤ m)) witMid) with hwitMid₂_def
        let empty2 : pSpec₂.Transcript (⟨0, hn1⟩ : Fin n).castSucc := fun i => i.elim0
        -- the phase-1 prefix is invariant under the phase-2 concat (crossing version)
        have htrFstEq : HEq (Transcript.concat msg tr).fst tr.fst :=
          concat_fst_heq_phase2 hlt tr msg
        -- the phase-2 tail seam at the crossing collapses to `empty2.concat msg₂`: reuse the
        -- interior seam lemma, then reconcile the empty prefix (`trs ≍ empty2`, both subsingleton)
        -- and the `msg` recast (`cast hmsgty₂ msg ≍ cast hmsgty0 msg`).
        have hsnd : HEq (Transcript.concat msg tr).snd (empty2.concat (cast hmsgty0 msg)) := by
          refine HEq.trans (concat_snd_heq_phase2 hlt tr msg hmsgty₂) ?_
          apply Function.hfunext
          · congr 1; simp only [Fin.val_succ, Fin.val_mk]; omega
          · intro a a' haa'
            have haa : (a : ℕ) = (a' : ℕ) := by
              have := Fin.heq_ext_iff (by simp only [Fin.val_succ, Fin.val_mk]; omega) |>.mp haa'
              omega
            simp only [Transcript.concat, Fin.snoc]
            obtain ⟨av, hav_lt⟩ := a
            obtain ⟨av', hav'_lt⟩ := a'
            simp only [Fin.val_mk] at haa hav_lt hav'_lt
            -- at the crossing `roundIdx - m = 0`, both snocs are at their (unique) last position
            rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
                dif_neg (show ¬ av' < 0 from by omega)]
            refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
            exact HEq.trans (cast_heq hmsgty₂ msg) (cast_heq hmsgty0 msg).symm
        have hPrev₂ : kSF₂.toFun (⟨0, hn1⟩ : Fin n).succ (verify stmt₁ trFst)
            (empty2.concat (cast hmsgty0 msg)) witMid₂ := by
          convert hPrev using 2 <;>
            first
              | (simp only [Fin.val_succ, Fin.val_mk]; omega)
              | -- statement: `verify stmt₁ trFst = verify stmt₁ <(concat msg tr).fst>`
                (congr 1;
                 exact eq_of_heq (HEq.trans htrFst_heq (HEq.trans htrFstEq.symm (cast_heq _ _).symm)))
              | -- transcript: `empty2.concat msg₂ ≍ <(concat msg tr).snd>`
                exact hsnd.symm
              | exact HEq.trans hsnd.symm (cast_heq _ _).symm
              | -- witness: `witMid₂ ≍ <cast (appendWitMid_gt) witMid>` — unfold the `set` def via
                -- `simp` (it handles the HEq motive), then peel the cast.
                (simp only [hwitMid₂_def]; exact cast_heq _ _)
        -- (2) `kSF₂.toFun_next 0` descends `hPrev₂` to `kSF₂.toFun 0 (verify…) default (extractMid…)`.
        have hDir₂0 : pSpec₂.dir (⟨0, hn1⟩ : Fin n) = .P_to_V := by
          have : (⟨0, hn1⟩ : Fin n) = ⟨(roundIdx : ℕ) - m, by omega⟩ := by
            ext; simp only [Fin.val_mk]; omega
          rw [this]; exact hDir₂
        have hStep := kSF₂.toFun_next (⟨0, hn1⟩ : Fin n) hDir₂0 (verify stmt₁ trFst)
          empty2 (cast hmsgty0 msg) witMid₂ hPrev₂
        -- `0.castSucc = 0` and `empty2 = default`: reshape `hStep` into `kSF₂.toFun 0 … default …`.
        have hcs0 : (⟨0, hn1⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by ext; simp
        set witE2 : WitMid₂ (0 : Fin (n + 1)) :=
          E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
            (empty2.concat (cast hmsgty0 msg)) witMid₂ with hwitE2_def
        have hStep0 : kSF₂.toFun (0 : Fin (n + 1)) (verify stmt₁ trFst) default
            (cast (congrArg WitMid₂ hcs0) witE2) := by
          rw [hwitE2_def]
          refine (kToFun_congr kSF₂.toFun hcs0 (verify stmt₁ trFst) ?_ ?_).mp hStep
          · -- `empty2 ≍ default` (both empty over `Fin 0` / the subsingleton transcript)
            refine HEq.trans (HEq.rfl : empty2 ≍ empty2) ?_
            apply Function.hfunext (by rw [hcs0])
            intro a _ _; exact a.elim0
          · exact (cast_heq _ _).symm
        -- (3) `kSF₂.toFun_empty` → `(verify stmt₁ trFst, cast E₂.eqIn witE2') ∈ rel₂`.
        have hMem : (verify stmt₁ trFst,
            cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) ∈ rel₂ :=
          (kSF₂.toFun_empty (verify stmt₁ trFst) (cast (congrArg WitMid₂ hcs0) witE2)).mpr hStep0
        -- (4) deterministic-run positivity + `kSF₁.toFun_full` yields the goal.
        have hPr := run_pos_of_mem_rel (impl := impl) (init := init) verify hVerify hInit stmt₁ trFst
          (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) hMem
        have hFull := kSF₁.toFun_full stmt₁ trFst
          (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) hPr
        -- Transport `hFull` (`kSF₁.toFun (last m) stmt₁ trFst (E₁.extractOut …)`) to the goal.
        -- The goal's witness is `cast (appendWitMid_le hcs) (append.extractMid roundIdx …)`, which by
        -- `appendExtractMid_cross` equals `E₁.extractOut stmt₁ trFst (cast E₂.eqIn (E₂.extractMid 0 …))`.
        have hExtEq : HEq (cast (appendWitMid_le hcs)
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
                (Transcript.concat msg tr) witMid))
            (E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
                (empty2.concat (cast hmsgty0 msg)) witMid₂))) :=
          (cast_heq _ _).trans (appendExtractMid_cross E₁ E₂ verify roundIdx hcross hn1 stmt₁
            (Transcript.concat msg tr) witMid trFst (htrFstEq.trans htrFst_heq.symm)
            (empty2.concat (cast hmsgty0 msg)) hsnd witMid₂
            (by rw [hwitMid₂_def]; exact ((cast_heq _ _).trans (cast_heq _ _)).symm))
        -- `hFull`'s extractOut argument and `hExtEq`'s coincide: both apply `E₂.extractMid 0` to the
        -- round-1 transcript `empty2.concat msg₂`. (`witE2` is *defined* as that `extractMid` call.)
        have hWitOut : E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2))
            = E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
                (empty2.concat (cast hmsgty0 msg)) witMid₂)) := by
          have hcc : cast (congrArg WitMid₂ hcs0) witE2 = witE2 := eq_of_heq (cast_heq _ _)
          rw [hcc, hwitE2_def]
        rw [hWitOut] at hFull
        -- Now transport `hFull` to the goal across index/transcript/witness coherences.
        refine Eq.mp ?_ hFull
        exact kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by rw [Fin.val_last, Fin.coe_castSucc]; exact hcross.symm) :
            (Fin.last m)
              = (⟨(roundIdx : Fin (m + n)).castSucc, by simp only [Fin.coe_castSucc]; omega⟩
                : Fin (m + 1)))
          stmt₁ (htrFst_heq.trans (cast_heq _ _).symm) hExtEq.symm
      · -- PHASE-2 INTERIOR (`m < roundIdx`): goal's `roundIdx.castSucc.val = roundIdx > m` → `kSF₂`.
        have hgt : m < (roundIdx : ℕ) := lt_of_le_of_ne hlt (Ne.symm hcross)
        have hncs : ¬ ((roundIdx : ℕ) ≤ m) := by omega
        simp only [Fin.val_castSucc, dif_neg hncs]
        -- The phase-2 truncated witness, reindexed to `⟨roundIdx-m,_⟩.succ`.
        set wit₂ : WitMid₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ :=
          cast (show WitMid₂ ⟨((roundIdx : Fin (m + n)).succ : ℕ) - m, by simp only [Fin.val_succ]; omega⟩
              = WitMid₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ from by
                congr 1; ext; simp only [Fin.val_succ, Fin.val_mk]; omega)
            (cast (appendWitMid_gt hnsucc) witMid) with hwit₂_def
        -- The shared transcript-tail seam.
        have htrEq : HEq (Transcript.concat msg tr).snd (trs.concat (cast hmsgty₂ msg)) :=
          concat_snd_heq_phase2 hlt tr msg hmsgty₂
        -- The phase-1 prefix is invariant under the phase-2 concat.
        have htrFstEq : HEq (Transcript.concat msg tr).fst tr.fst :=
          concat_fst_heq_phase2 hlt tr msg
        -- `hPrev` reshaped to `kSF₂.toFun (succ) (verify stmt₁ trFst) (trs.concat msg₂) wit₂`.
        have hPrev₂ : kSF₂.toFun (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ
            (verify stmt₁ trFst) (trs.concat (cast hmsgty₂ msg)) wit₂ := by
          convert hPrev using 2 <;>
            first
              | (simp only [Fin.val_succ, Fin.val_mk]; omega)
              | -- statement: `verify stmt₁ trFst = verify stmt₁ <(concat msg tr).fst>`
                (congr 1;
                 exact eq_of_heq (HEq.trans htrFst_heq (HEq.trans htrFstEq.symm (cast_heq _ _).symm)))
              | -- transcript: `trs.concat msg₂ ≍ <(concat msg tr).snd>`
                exact htrEq.symm
              | exact HEq.trans htrEq.symm (cast_heq _ _).symm
              | -- witness: `wit₂ ≍ <cast (appendWitMid_gt) witMid>` — unfold the `set` def via simp,
                -- then peel the cast.
                (simp only [hwit₂_def]; exact cast_heq _ _)
        -- Apply `kSF₂.toFun_next` and transport to the goal via `appendExtractMid_gt`.
        have key := kSF₂.toFun_next ⟨(roundIdx : ℕ) - m, by omega⟩ hDir₂ (verify stmt₁ trFst)
          trs (cast hmsgty₂ msg) wit₂ hPrev₂
        -- Identify the goal's witness `cast _ (append.extractMid …)` with `key`'s
        -- `E₂.extractMid ⟨roundIdx-m,_⟩ (verify stmt₁ trFst) (trs.concat msg₂) wit₂`.
        have hExtEq : HEq (cast (appendWitMid_gt hncs)
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
                (Transcript.concat msg tr) witMid))
            (E₂.extractMid ⟨(roundIdx : ℕ) - m, by omega⟩ (verify stmt₁ trFst)
              (trs.concat (cast hmsgty₂ msg)) wit₂) :=
          (cast_heq _ _).trans (appendExtractMid_gt E₁ E₂ verify roundIdx hgt stmt₁
            (Transcript.concat msg tr) witMid trFst (htrFstEq.trans htrFst_heq.symm)
            (trs.concat (cast hmsgty₂ msg)) htrEq wit₂
            (by rw [hwit₂_def]; exact ((cast_heq _ _).trans (cast_heq _ _)).symm))
        -- Close the goal by transporting `key` across the index/statement/transcript/witness
        -- coherences. The goal's verify-statement is on `tr.fst`; `key`'s is on `trFst`; equal.
        -- `convert` auto-unifies the defeq legs; the remaining goals are dispatched uniformly.
        convert key using 2 <;>
          first
            | (apply Fin.ext; omega)
            | (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) htrFst_heq.symm))
            | exact cast_heq _ _
            | exact hExtEq
            | exact hExtEq.symm
            | exact eq_of_heq hExtEq
            | exact (eq_of_heq hExtEq).symm
  -- `toFun_full`: at the last round the appended verifier's output factors through `V₂` on
  -- `verify stmt₁ tr.fst` (the `Verifier.append` run, which `pure`-binds `V₁`'s deterministic
  -- output), and `extractOut` composes as `E₁.extractOut ∘ (cast E₂.eqIn) ∘ E₂.extractOut` (for
  -- `n > 0`, directly `E₂.extractOut`). With the run collapse `(V₁.append V₂).run stmt₁ tr =
  -- V₂.run (verify stmt₁ tr.fst) tr.snd` (proven inline in `StateFunction.append.toFun_full`,
  -- `Append.lean:1646–1652 / 1673–1679`), the positive-probability hypothesis transfers to `V₂`, and
  -- `kSF₂.toFun_full` (for `n > 0`) / `kSF₁.toFun_full` composed through the empty phase-2
  -- `E₂.eqIn` round-trip (for `n = 0`) yields the goal. Mirrors `StateFunction.append.toFun_full`
  -- with the witness leg threaded through `Extractor.RoundByRound.append`'s `extractOut`.
  toFun_full := by
    intro stmt₁ tr witOut hPos
    -- The full-transcript `.fst`/`.snd` agree (over `HEq`) with the partial-transcript projections
    -- at the last round (`min (m+n) m = m`, `(m+n) - m = n`). Copied verbatim from
    -- `StateFunction.append.toFun_full`.
    have hmincard : min ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) m = m := by
      simp only [Fin.val_last]; omega
    have hsndcard : ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) - m = n := by
      simp only [Fin.val_last]; omega
    have htFstHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.fst (k := Fin.last (m + n)) T) ≍ FullTranscript.fst T := by
      intro T
      apply Function.hfunext (congrArg Fin hmincard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hmincard |>.mp ha; omega
      simp only [Transcript.fst, FullTranscript.fst]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_castAdd]; omega
    have htSndHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.snd (k := Fin.last (m + n)) T) ≍ FullTranscript.snd T := by
      intro T
      apply Function.hfunext (congrArg Fin hsndcard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hsndcard |>.mp ha; omega
      simp only [Transcript.snd, FullTranscript.snd]
      rw [dif_neg (show ¬ (Fin.last (m + n)) ≤ m from by simp only [Fin.val_last]; omega)]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_natAdd]; omega
    by_cases hn : n = 0
    · -- degenerate: empty second protocol. The last round index is `m ≤ m`, so `toFun (last)`
      -- lands in the `kSF₁` branch. The appended `extractOut` crosses through the trivial empty
      -- phase-2 `E₂.extractOut`/`eqIn` round-trip into `E₁.extractOut`.
      subst hn
      rw [dif_pos (show ((Fin.last (m + 0)) : ℕ) ≤ m from by simp)]
      -- The phase-1 prefix as a genuine full transcript.
      set trFst : pSpec₁.FullTranscript := (FullTranscript.fst tr : pSpec₁.FullTranscript)
        with htrFst
      -- The appended run collapses to `V₂.run (verify stmt₁ trFst) tr.snd` (deterministic `V₁`
      -- `pure`-binds). Copied verbatim from `StateFunction.append.toFun_full`.
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ trFst) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ trFst))) (FullTranscript.snd tr)) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun] at hPos
      -- `kSF₂.toFun_full` (over the empty phase 2, `last 0`) yields the phase-2 leg, which since
      -- `n = 0` is the round-`0` state — `kSF₂.toFun_empty` then puts `(verify …, cast eqIn …)` in
      -- `rel₂`, supplying the `kSF₁.toFun_full` positivity via deterministic-run positivity.
      have hPr2 := kSF₂.toFun_full (verify stmt₁ trFst) (FullTranscript.snd tr) witOut hPos
      -- `kSF₂.toFun (last 0) … (E₂.extractOut …)`; reindex `last 0 = 0` and `tr.snd = default`.
      have hl0 : (Fin.last 0 : Fin (0 + 1)) = (0 : Fin (0 + 1)) := by ext; simp
      have hPr2' : kSF₂.toFun (0 : Fin (0 + 1)) (verify stmt₁ trFst) default
          (cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut)) := by
        refine (kToFun_congr kSF₂.toFun hl0 (verify stmt₁ trFst) ?_ ?_).mp hPr2
        · apply Function.hfunext (by rw [hl0]); intro a _ _; exact a.elim0
        · exact (cast_heq _ _).symm
      -- `kSF₂.toFun_empty` then gives `(verify stmt₁ trFst, cast E₂.eqIn …) ∈ rel₂`.
      have hMem : (verify stmt₁ trFst,
          cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) ∈ rel₂ :=
        (kSF₂.toFun_empty (verify stmt₁ trFst) (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))).mpr hPr2'
      -- deterministic-run positivity + `kSF₁.toFun_full` yields the phase-1 goal.
      have hPr1 := run_pos_of_mem_rel (impl := impl) (init := init) verify hVerify hInit stmt₁ trFst
        (cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) hMem
      have hFull := kSF₁.toFun_full stmt₁ trFst
        (cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) hPr1
      -- Identify `hFull`'s `E₂.extractOut` argument with the one in `appendExtractOut_eq0` (peel the
      -- redundant `cast (congrArg WitMid₂ hl0)`), then transport across the index/transcript/witness
      -- coherences. `hFull`'s `last m`; goal's `⟨m+0,_⟩`.
      have hcc : cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut)
          = E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut :=
        eq_of_heq (cast_heq _ _)
      rw [hcc] at hFull
      -- Inline the empty-phase-2 `extractOut` HEq (the `n = 0` analogue of `appendExtractOut_gt`):
      -- the appended `extractOut` crosses immediately via `E₁.extractOut` after the trivial empty
      -- phase-2 `E₂.extractOut`/`eqIn` round-trip.
      have hExtEq : HEq (cast (appendWitMid_le (show ((Fin.last (m + 0)) : ℕ) ≤ m from by simp))
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
          (E₁.extractOut stmt₁ trFst
            (cast E₂.eqIn (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) := by
        refine HEq.trans (cast_heq _ _) ?_
        unfold Extractor.RoundByRound.append
        dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
        simp only [dif_pos (show (0 : ℕ) = 0 from rfl), id_eq]
        refine HEq.trans ?_ (HEq.refl (E₁.extractOut stmt₁ trFst
          (cast E₂.eqIn (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))))
        rw [eq_mpr_eq_cast]
        exact cast_heq _ _
      refine Eq.mp ?_ hFull
      exact kToFun_congr₁ kSF₁.toFun
        (Fin.ext (by simp only [Fin.val_last]; omega) :
          (Fin.last m) = ⟨(Fin.last (m + 0) : Fin (m + 0 + 1)), by simp only [Fin.val_last]; omega⟩)
        stmt₁ ((htFstHeq tr).symm.trans (cast_heq _ _).symm) hExtEq.symm
    · -- `n > 0`: last round index `m + n > m`, so `toFun (last)` lands in the `kSF₂` branch.
      rw [dif_neg (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega)]
      -- The appended run collapses to `V₂.run (verify stmt₁ tr.fst) tr.snd`. Copied verbatim from
      -- `StateFunction.append.toFun_full`.
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ (FullTranscript.fst tr)))) _) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun] at hPos
      -- transfer the positive-probability hypothesis to `kSF₂.toFun_full`.
      have hPr := kSF₂.toFun_full (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr)
        witOut hPos
      -- `hPr : kSF₂.toFun (last n) (verify stmt₁ tr.fst) tr.snd (E₂.extractOut …)`.
      -- The goal is `kSF₂.toFun ⟨(m+n)-m,_⟩ (verify stmt₁ <Transcript.fst tr>) <Transcript.snd tr>
      --   (cast (appendWitMid_gt …) (append.extractOut …))`. `convert` auto-unifies the defeq legs;
      -- the remaining goals (index / verify-statement / .snd transcript / witness) are dispatched by
      -- the `htFstHeq`/`htSndHeq` projection agreements and `appendExtractOut_gt` (witness),
      -- mirroring the `hNeg'` step of `StateFunction.append.toFun_full`.
      have hExtEq : HEq (cast (appendWitMid_gt
              (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega))
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
          (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) witOut) :=
        appendExtractOut_gt E₁ E₂ verify (by omega) stmt₁ tr witOut
          (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega)
      convert hPr using 2 <;>
        first
          | (simp only [Fin.val_last]; omega)
          | (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) (htFstHeq tr)))
          | exact htSndHeq tr
          | exact hExtEq
          | exact hExtEq.symm

/-! ## Unconditional round-by-round *knowledge* soundness append keystone

With the composite knowledge state function `KnowledgeStateFunction.append` now fully proven
(`toFun_empty` / `toFun_next` / `toFun_full` all axiom-clean above), the round-by-round knowledge
soundness append keystone can be stated **without** the `kSF` residual that
`AppendRbrKeystone.lean`'s `append_rbrKnowledgeSoundness_keystone` carried: the composite knowledge
state function is supplied internally from `KnowledgeStateFunction.append`, and the two destructured
per-round knowledge bounds `hBound₁` / `hBound₂` are taken via the input verifiers' own
`rbrKnowledgeSoundness` hypotheses `h₁` / `h₂`.

The remaining content is the *per-round probabilistic bound* against the concrete composite objects:
phase-1 is a runWithLog-level port of the soundness phase-1 seam reduction (reducing to `hBound₁`),
and phase-2 reduces to `hBound₂` *for all input statements* (the no-`langIn` quantification of
`rbrKnowledgeSoundness`, `RoundByRound.lean:839` — which is precisely why the knowledge keystone is
closeable where the plain-soundness phase-2 `appendRbrSoundnessPhase2Residual` is irreducible). That
per-round bound is isolated as the single typed residual
`appendRbrKnowledgeSoundnessPerRoundResidual`, stated directly against the proven composite
`KnowledgeStateFunction.append` and `Extractor.RoundByRound.append` with the destructured inner
extractors and bounds in scope, so no `sorry` is introduced and the kSF/extractor existential is fully
assembled from proven objects. -/

/-- **Per-round bound residual of the unconditional round-by-round knowledge soundness append
keystone.** The appended per-round knowledge flip-event probability, stated against the *proven*
composite knowledge state function `KnowledgeStateFunction.append` and the proven composite extractor
`Extractor.RoundByRound.append`. This is the genuine remaining probabilistic content of
`append_rbrKnowledgeSoundness_keystone_unconditional`: the witness-threaded per-round seam analysis,
phase-1 reducing to `kSF₁`/`E₁` and phase-2 (via the no-`langIn` quantification of
`rbrKnowledgeSoundness`) reducing to `kSF₂`/`E₂`. -/
def appendRbrKnowledgeSoundnessPerRoundResidual {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0} : Prop :=
  ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
  ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂),
  ∀ i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx,
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.castSucc stmtIn transcript
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
              (transcript.concat challenge) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i

/-- **Unconditional round-by-round knowledge soundness append keystone, deterministic-`V₁`
message-seam case.**

Removes the `kSF` residual of `append_rbrKnowledgeSoundness_keystone`: the composite knowledge state
function is supplied internally from the *proven* `KnowledgeStateFunction.append`, the composite
extractor from the proven `Extractor.RoundByRound.append`, and the two inner per-round knowledge
bounds are taken via the input verifiers' own `rbrKnowledgeSoundness` hypotheses `h₁` / `h₂` (which
also furnish the inner knowledge state functions `kSF₁` / `kSF₂` fed to `KnowledgeStateFunction.append`).

The only remaining content is the per-round probabilistic bound against these concrete composite
objects, isolated as the typed residual `appendRbrKnowledgeSoundnessPerRoundResidual` (`hPerRound`).
Unlike the plain-soundness phase-2 obstruction, this residual *is* discharchable in principle — the
inner bound `hBound₂` from `h₂` quantifies over **all** input statements (no `∉ langIn` restriction;
`RoundByRound.lean:839`), so the random seam statement `verify stmtIn tr.fst ∈ lang₂` is controlled.
This keystone is fully axiom-clean (no `sorry`); it pins the appended knowledge soundness existential
entirely onto proven composite objects, leaving only the witness-threaded per-round seam analysis. -/
theorem append_rbrKnowledgeSoundness_keystone_unconditional
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    (hPerRound : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgeSoundnessPerRoundResidual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit (rbrKnowledgeError₁ := rbrKnowledgeError₁)
        (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, _hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, _hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    hPerRound kSF₁ kSF₂⟩

end Verifier

-- Axiom audit for the sorry-free bricks: each should report only
-- `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.appendWitMid_le
#print axioms Verifier.appendWitMid_gt
#print axioms Verifier.appendExtractMid_le
#print axioms Verifier.appendExtractMid_gt
#print axioms Verifier.appendExtractMid_cross
#print axioms Verifier.appendExtractOut_gt
#print axioms Verifier.kToFun_congr
#print axioms Verifier.kToFun_congr₁
#print axioms Verifier.concat_fst_heq_phase1
#print axioms Verifier.KnowledgeStateFunction.append
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
