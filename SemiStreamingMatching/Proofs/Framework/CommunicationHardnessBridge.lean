import SemiStreamingMatching.Proofs.Framework.CommunicationHardness

open scoped BigOperators

namespace Formal.Streaming

namespace HardDistribution

open SimpleExpansion AugmentedExpansion

variable {L0 R0 : Type} {r t : ℕ}
  [Fintype L0] [Fintype R0] [DecidableEq L0] [DecidableEq R0]

private theorem natCast_le_sum_natCast_of_le_sum
    {α : Type} [Fintype α] (n : ℕ) (f : α → ℕ)
    (h : n ≤ ∑ x, f x) :
    (n : ℝ) ≤ ∑ x, (f x : ℝ) := by
  rw [← Nat.cast_sum]
  exact (Nat.cast_le).2 h

private theorem belongingEdges_eq_of_instances
    {Ω S E : Type}
    (fΩ₁ fΩ₂ : Fintype Ω) (fE₁ fE₂ : Fintype E)
    (d₁ d₂ : DecidableEq S) (eta : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (s : S) :
    @UniformPosterior.belongingEdges Ω S E fΩ₁ fE₁ d₁ eta summary present s =
      @UniformPosterior.belongingEdges Ω S E fΩ₂ fE₂ d₂ eta summary present s := by
  have hΩ : fΩ₁ = fΩ₂ := Subsingleton.elim _ _
  have hE : fE₁ = fE₂ := Subsingleton.elim _ _
  have hdec : d₁ = d₂ := Subsingleton.elim _ _
  subst fΩ₂
  subst fE₂
  subst d₂
  rfl

set_option maxHeartbeats 1000000

theorem exactRecoverableSpecialSumBound_of_compression
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (bits threshold : ℕ) (eta beta : ℚ)
    (rate logBound : ℝ)
    (hrate0 : 0 < rate)
    (hlogBound0 : 0 ≤ logBound)
    (hpositive : ∀ J p, (part B H J p).Nonempty → 0 < deletions p)
    (hhalf : ∀ J p, (part B H J p).Nonempty →
      2 * deletions p ≤ (part B H J p).card)
    (hrate : ∀ J p, (part B H J p).Nonempty →
      rate ≤ (deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p})
    (hlog : ∀ J p, (part B H J p).Nonempty →
      Real.log (Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1) ≤
        logBound)
    (hetaRate : (eta : ℝ) ≤ rate / 2)
    (hnumeric :
      20 * (B.P : ℝ) ^ 2 / ((t : ℝ) * rate) *
          ((bits : ℝ) * Real.log 2 + logBound) ≤
        (beta : ℝ) * (threshold + 1)) :
    ExactRecoverableSpecialSumBound B H deletions hdeletions
      bits threshold eta beta := by
  classical
  intro prot hprot
  let W := protocolPosteriorModel B H deletions hdeletions
    (fun sample ↦ exactSampleCertificate sample) (fun _ ↦ rfl) prot
  letI : Fintype W.Summary := W.summaryFintype
  let posteriorSummaryDecEq : DecidableEq W.Summary := W.summaryDecidableEq
  letI : DecidableEq W.Summary := posteriorSummaryDecEq
  simp only [protocolPosteriorModel]
  let defaultSummaryDecEq :
      DecidableEq (IndexTuple B t × prot.TranscriptCode) := instDecidableEqProd
  let targetSampleFintype : Fintype (Sample B H deletions) := inferInstance
  let targetEdgeFintype : Fintype
      (Edge (AugmentedExpansion.Left (L := L0) (R := R0) B)
        (AugmentedExpansion.Right (L := L0) (R := R0) B)) := inferInstance
  let count : Sample B H deletions → ℕ := fun sample ↦
    ((@UniformPosterior.belongingEdges
        (Sample B H deletions)
        (IndexTuple B t × prot.TranscriptCode)
        (Edge (AugmentedExpansion.Left (L := L0) (R := R0) B)
          (AugmentedExpansion.Right (L := L0) (R := R0) B))
        targetSampleFintype targetEdgeFintype posteriorSummaryDecEq
        eta (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot sample)) ∩
      potentialSpecialEdges B H
        (protocolSummary B H deletions prot sample).1).card
  let originalCount : Sample B H deletions → ℕ := fun sample ↦
    ((@UniformPosterior.belongingEdges
        (Sample B H deletions)
        (IndexTuple B t × prot.TranscriptCode)
        (Edge (AugmentedExpansion.Left (L := L0) (R := R0) B)
          (AugmentedExpansion.Right (L := L0) (R := R0) B))
        targetSampleFintype targetEdgeFintype defaultSummaryDecEq
        eta (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot sample)) ∩
      potentialSpecialEdges B H sample.1).card
  have count_eq_original (sample : Sample B H deletions) :
      count sample = originalCount sample := by
    dsimp only [count, originalCount]
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_inter]
    rw [belongingEdges_eq_of_instances targetSampleFintype targetSampleFintype
      targetEdgeFintype targetEdgeFintype posteriorSummaryDecEq defaultSummaryDecEq]
    rw [show (protocolSummary B H deletions prot sample).1 = sample.1 by
      simp only [protocolSummary]]
  have hcount :
      (∑ sample : Sample B H deletions, (count sample : ℚ)) ≤
        beta * (threshold + 1) * Fintype.card (Sample B H deletions) := by
    let localFactor : ℝ :=
      ((B.P : ℝ) / t) *
        ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound))
    let globalFactor : ℝ :=
      20 * (B.P : ℝ) ^ 2 / ((t : ℝ) * rate) *
        ((bits : ℝ) * Real.log 2 + logBound)
    have hglobal :
        (∑ sample : Sample B H deletions, (count sample : ℝ)) ≤
          Fintype.card (Sample B H deletions) * globalFactor := by
      calc
        _ = ∑ sample : Sample B H deletions,
            (originalCount sample : ℝ) := by
          apply Finset.sum_congr rfl
          intro sample _hsample
          rw [count_eq_original]
        _ ≤ ∑ sample : Sample B H deletions,
            ∑ p : Fin B.P,
              ((playerRecoverableSpecialEdges B H deletions hdeletions prot
                sample p).card : ℝ) := by
          apply Finset.sum_le_sum
          intro sample _hsample
          have hcharge : originalCount sample ≤
              ∑ p : Fin B.P,
                (playerRecoverableSpecialEdges B H deletions hdeletions prot
                  sample p).card := by
            dsimp only [originalCount, defaultSummaryDecEq]
            exact globalRecoverableSpecial_card_le_sum_player
              B H deletions hdeletions prot sample rate hpositive hrate hetaRate
          exact natCast_le_sum_natCast_of_le_sum
            (originalCount sample)
            (fun p ↦ (playerRecoverableSpecialEdges B H deletions hdeletions prot
              sample p).card)
            hcharge
        _ = ∑ p : Fin B.P,
            ∑ sample : Sample B H deletions,
              ((playerRecoverableSpecialEdges B H deletions hdeletions prot
                sample p).card : ℝ) := by
          rw [Finset.sum_comm]
        _ ≤ ∑ _p : Fin B.P,
            Fintype.card (Sample B H deletions) * localFactor := by
          apply Finset.sum_le_sum
          intro p _hp
          simpa only [localFactor] using
            sum_playerRecoverableSpecialEdges_le B H deletions hdeletions prot
              hprot p rate logBound hrate0 hlogBound0 hpositive hhalf hrate hlog
        _ = Fintype.card (Sample B H deletions) * globalFactor := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          push_cast
          rw [Fintype.card_fin]
          dsimp [localFactor, globalFactor]
          ring
    have hglobal' :
        (∑ sample : Sample B H deletions, (count sample : ℝ)) ≤
          (beta : ℝ) * (threshold + 1) *
            Fintype.card (Sample B H deletions) := by
      calc
        _ ≤ Fintype.card (Sample B H deletions) * globalFactor := hglobal
        _ ≤ Fintype.card (Sample B H deletions) *
            ((beta : ℝ) * (threshold + 1)) :=
          mul_le_mul_of_nonneg_left hnumeric (by positivity)
        _ = _ := by ring
    apply (Rat.cast_le (K := ℝ)).mp
    rw [Rat.cast_sum]
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_one]
    exact hglobal'
  calc
    _ = ∑ sample : Sample B H deletions, (count sample : ℚ) := by
      apply Finset.sum_congr rfl
      intro sample _hsample
      norm_cast
    _ ≤ _ := hcount

end HardDistribution

end Formal.Streaming
