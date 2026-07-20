import SemiStreamingMatching.Proofs.Framework.DeletionExpectation
import SemiStreamingMatching.Proofs.Framework.ERSDensity
import SemiStreamingMatching.Proofs.Framework.Framework
import SemiStreamingMatching.Proofs.Framework.GoodEventCommunication
import SemiStreamingMatching.Proofs.Framework.RelabelCommunication

namespace Formal.Streaming

open scoped BigOperators

namespace FinitePartitionDistribution

variable {P : ℕ} {L R : Type*}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem IsHardForCommunication.mono_success
    {D : FinitePartitionDistribution P L R} {rho p p' : ℚ} {bits : ℕ}
    (hD : D.IsHardForCommunication rho p bits) (hpp' : p ≤ p') :
    D.IsHardForCommunication rho p' bits := by
  intro prot hprot
  exact (hD prot hprot).trans
    (mul_le_mul_of_nonneg_right hpp' (by positivity))

end FinitePartitionDistribution

namespace HardDistribution

open SimpleExpansion AugmentedExpansion

variable {L R : Type} {r t : ℕ}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

set_option maxHeartbeats 3000000 in

theorem communicationHardness_of_good_exactRecoverableSpecialSum_assembly
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    {deletionAllowance specialThreshold bits : ℕ}
    {rho eta beta pBad : ℚ}
    (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hgap : ∀ sample : Sample B H deletions,
      CanonicalDeletionGood deletionAllowance sample →
      (((exactSampleCertificate sample).ordinaryUpper +
          specialThreshold : ℕ) : ℚ) <
        rho * (exactSampleCertificate sample).optimumLower)
    (hbad :
      ((canonicalDeletionBadSamples (B := B) (H := H) (q := deletions)
        deletionAllowance).card : ℚ) ≤
          pBad * Fintype.card (Sample B H deletions))
    (hsum : ExactRecoverableSpecialSumBound
      (L0 := L) (R0 := R) (r := r) (t := t)
      B H deletions hdeletions bits specialThreshold eta beta) :
    (finitePartitionDistribution B H deletions hdeletions).IsHardForCommunication
      rho (pBad + (1 - eta + beta)) bits := by
  let D := finitePartitionDistribution B H deletions hdeletions
  have hbadD : ((D.badSamples
      (CanonicalDeletionGood deletionAllowance)).card : ℚ) ≤
        pBad * Fintype.card D.Sample := by
    simpa only [D, FinitePartitionDistribution.badSamples,
      canonicalDeletionBadSamples] using hbad
  apply D.isHardForCommunication_of_good_posterior_recovery
    (fun sample ↦ exactSampleCertificate sample)
    (CanonicalDeletionGood deletionAllowance) heta1 hrho hgap hbadD
    (fun prot _hprot ↦
      protocolPosteriorModel B H deletions hdeletions
        (fun sample ↦ exactSampleCertificate sample) (fun _ ↦ rfl) prot)
  intro prot hprot
  exact hsum prot hprot

end HardDistribution

namespace ERSFamily

namespace DenseERSSequence

open SimpleExpansion AugmentedExpansion HardDistribution

variable {B : SimpleProperBlueprint}

theorem augmented_left_card (F : DenseERSSequence B.C) (k : ℕ) :
    Fintype.card
        (AugmentedExpansion.Left
          (L := Fin (F.n k)) (R := Fin (F.n k)) B) =
      F.augmentedExpansionSize B.P k := by
  classical
  simp [ERSSequence.augmentedExpansionSize, SimpleExpansion.Left,
    SimpleExpansion.Right, Fintype.card_pi]
  omega

theorem augmented_right_card (F : DenseERSSequence B.C) (k : ℕ) :
    Fintype.card
        (AugmentedExpansion.Right
          (L := Fin (F.n k)) (R := Fin (F.n k)) B) =
      F.augmentedExpansionSize B.P k := by
  classical
  simp [ERSSequence.augmentedExpansionSize, SimpleExpansion.Left,
    SimpleExpansion.Right, Fintype.card_pi]
  omega

noncomputable def augmentedLeftEquivFin (F : DenseERSSequence B.C) (k : ℕ) :
    AugmentedExpansion.Left
        (L := Fin (F.n k)) (R := Fin (F.n k)) B ≃
      Fin (F.augmentedExpansionSize B.P k) :=
  Fintype.equivFinOfCardEq (F.augmented_left_card k)

noncomputable def augmentedRightEquivFin (F : DenseERSSequence B.C) (k : ℕ) :
    AugmentedExpansion.Right
        (L := Fin (F.n k)) (R := Fin (F.n k)) B ≃
      Fin (F.augmentedExpansionSize B.P k) :=
  Fintype.equivFinOfCardEq (F.augmented_right_card k)

structure ERSHardFamilyCertificate (B : SimpleProperBlueprint)
    (F : DenseERSSequence B.C) (epsilon : ℚ) where

  deletions : (k : ℕ) → Fin B.P → ℕ

  deletionAllowance : ℕ → ℕ

  specialThreshold : ℕ → ℕ

  gapError : ℚ

  posteriorEta : ℚ

  posteriorBeta : ℚ

  deletionBadMass : ℚ

  communicationScale : ℕ
  epsilon_pos : 0 < epsilon
  gapError_nonneg : 0 ≤ gapError
  gapError_le_half : gapError ≤ 1 / 2
  posteriorEta_le_one : posteriorEta ≤ 1
  deletion_admissible : ∀ k J p,
    deletions k p ≤ (part B (F.host k) J p).card

  deletion_bad_bound : ∀ k,
    CanonicalDeletionBadBound B (F.host k) (deletions k)
      (deletionAllowance k) deletionBadMass
  side_capacity : ∀ k,
    B.edgeCount * (F.r k) ^ B.P + deletionAllowance k ≤
      2 * (F.n k) ^ B.P
  numerator_error : ∀ k,
    2 * (B.P * F.loss) +
        (specialThreshold k : ℚ) / ((F.n k) ^ B.P : ℕ) ≤ gapError
  denominator_error : ∀ k,
    B.P * F.loss +
        (deletionAllowance k : ℚ) / ((F.n k) ^ B.P : ℕ) ≤ gapError
  gap_slack : 8 * gapError < epsilon
  success_bound :
    deletionBadMass + (1 - posteriorEta + posteriorBeta) ≤ 1 - epsilon
  recoverableSpecial : ∀ k bits,
    communicationScale * bits ≤
        F.augmentedExpansionSize B.P k * F.t k →
      ExactRecoverableSpecialSumBound
        (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
        B (F.host k) (deletions k) (deletion_admissible k)
        bits (specialThreshold k) posteriorEta posteriorBeta

namespace ERSHardFamilyCertificate

variable {F : DenseERSSequence B.C} {epsilon : ℚ}

noncomputable def structuredDistribution
    (C : ERSHardFamilyCertificate B F epsilon) (k : ℕ) :=
  finitePartitionDistribution B (F.host k) (C.deletions k)
    (C.deletion_admissible k)

noncomputable def distribution
    (C : ERSHardFamilyCertificate B F epsilon) (k : ℕ) :
    FinitePartitionDistribution (B.P + 1)
      (Fin (F.augmentedExpansionSize B.P k))
      (Fin (F.augmentedExpansionSize B.P k)) :=
  (C.structuredDistribution k).relabel
    (F.augmentedLeftEquivFin k) (F.augmentedRightEquivFin k)

private theorem approximation_nonneg
    (C : ERSHardFamilyCertificate B F epsilon) :
    0 ≤ blueprintRatioRat B + epsilon := by
  have hratioReal : (0 : ℝ) ≤ (blueprintRatioRat B : ℝ) := by
    simpa only [blueprintRatioRat_cast] using blueprintRatio_nonneg B
  have hratio : (0 : ℚ) ≤ blueprintRatioRat B := by
    exact_mod_cast hratioReal
  linarith [C.epsilon_pos]

set_option maxHeartbeats 1200000 in

theorem gap_on_good (C : ERSHardFamilyCertificate B F epsilon) (k : ℕ)
    (sample : Sample B (F.host k) (C.deletions k))
    (hgood : CanonicalDeletionGood (C.deletionAllowance k) sample) :
    (((exactSampleCertificate sample).ordinaryUpper +
        C.specialThreshold k : ℕ) : ℚ) <
      (blueprintRatioRat B + epsilon) *
        (exactSampleCertificate sample).optimumLower := by
  have hdensity := F.canonical_density_bounds B k sample.1
  rw [canonicalMatching_card, expansion_left_card] at hdensity
  apply exactSampleCertificate_gap_of_good B (F.host k) sample hgood
    (qSpecial := C.specialThreshold k)
    (a := B.P * F.loss) (eta := C.gapError) (epsilon := epsilon)
  · simpa using C.side_capacity k
  · exact mul_nonneg (by positivity) F.loss_nonneg
  · exact C.gapError_nonneg
  · exact C.gapError_le_half
  · simpa using hdensity.1
  · simpa using hdensity.2
  · simpa using C.numerator_error k
  · simpa using C.denominator_error k
  · exact C.gap_slack

theorem deletion_bad_event_bound
    (C : ERSHardFamilyCertificate B F epsilon) (k : ℕ) :
    ((canonicalDeletionBadSamples
        (B := B) (H := F.host k) (q := C.deletions k)
        (C.deletionAllowance k)).card : ℚ) ≤
      C.deletionBadMass *
        Fintype.card (Sample B (F.host k) (C.deletions k)) := by
  exact (C.deletion_bad_bound k).card_le

set_option maxHeartbeats 1200000 in

theorem structured_communicationHard
    (C : ERSHardFamilyCertificate B F epsilon) (k bits : ℕ)
    (hbits : C.communicationScale * bits ≤
      F.augmentedExpansionSize B.P k * F.t k) :
    (C.structuredDistribution k).IsHardForCommunication
      (blueprintRatioRat B + epsilon) (1 - epsilon) bits := by
  have hraw :=
    communicationHardness_of_good_exactRecoverableSpecialSum_assembly
    B (F.host k) (C.deletions k) (C.deletion_admissible k)
    (deletionAllowance := C.deletionAllowance k)
    (specialThreshold := C.specialThreshold k) (bits := bits)
    (rho := blueprintRatioRat B + epsilon)
    (eta := C.posteriorEta) (beta := C.posteriorBeta)
    (pBad := C.deletionBadMass)
    C.posteriorEta_le_one C.approximation_nonneg
    (C.gap_on_good k) (C.deletion_bad_event_bound k)
    (C.recoverableSpecial k bits hbits)
  exact hraw.mono_success C.success_bound

theorem communicationHard
    (C : ERSHardFamilyCertificate B F epsilon) (k bits : ℕ)
    (hbits : C.communicationScale * bits ≤
      F.augmentedExpansionSize B.P k * F.t k) :
    (C.distribution k).IsHardForCommunication
      (blueprintRatioRat B + epsilon) (1 - epsilon) bits := by
  exact (C.structured_communicationHard k bits hbits).relabel
    (F.augmentedLeftEquivFin k) (F.augmentedRightEquivFin k)

noncomputable def toSequentialBlueprintHardFamily
    (C : ERSHardFamilyCertificate B F epsilon) :
    SequentialBlueprintHardFamily B where
  size := F.augmentedExpansionSize B.P
  hostMultiplicity := F.t
  distribution := C.distribution
  approximation := blueprintRatioRat B + epsilon
  successThreshold := 1 - epsilon
  communicationScale := C.communicationScale
  spaceDomination := by
    intro space hspace
    exact F.semiStreaming_space_domination B hspace C.communicationScale
  communicationHard := by
    intro k bits hbits
    exact C.communicationHard k bits hbits

@[simp]
theorem toSequentialBlueprintHardFamily_hasPaperParameters
    (C : ERSHardFamilyCertificate B F epsilon) :
    C.toSequentialBlueprintHardFamily.HasPaperParameters epsilon := by
  exact ⟨rfl, rfl⟩

theorem blueprint_to_semiStreaming_lower_bound
    (C : ERSHardFamilyCertificate B F epsilon)
    (A : SemiStreamingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (C.distribution k).Sample,
        (A.algorithm (F.augmentedExpansionSize B.P k)).successProbability
            (blueprintRatioRat B + epsilon)
            ((C.distribution k).input x).graph
            ((C.distribution k).input x).stream ≤ 1 - epsilon := by
  exact C.toSequentialBlueprintHardFamily.blueprint_to_semiStreaming_lower_bound
    C.toSequentialBlueprintHardFamily_hasPaperParameters A

end ERSHardFamilyCertificate

end DenseERSSequence

end ERSFamily

end Formal.Streaming
