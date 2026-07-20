import SemiStreamingMatching.Proofs.Framework.DeletionParameters
import SemiStreamingMatching.Proofs.Framework.ERSDensity
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

namespace DenseERSSequence

variable {C : ℕ}

open HardDistribution SimpleExpansion

theorem matchingSizesTendToInfinity (F : DenseERSSequence C) :
    SizesTendToInfinity F.r := by
  intro target
  let gap := F.relativeLossDenominator - F.relativeLossNumerator
  let scale := F.relativeLossDenominator * C
  have hgap : 0 < gap := Nat.sub_pos_of_lt F.relativeLoss_lt
  have hden : 0 < F.relativeLossDenominator :=
    Nat.zero_lt_of_lt F.relativeLoss_lt
  have hC : 0 < C := (F.host 0).C_pos
  have hscale : 0 < scale := Nat.mul_pos hden hC
  obtain ⟨k0, hk0⟩ := F.baseSizesGrow (scale * target)
  refine ⟨k0, fun k hk ↦ ?_⟩
  have hn : scale * target ≤ F.n k := hk0 k hk
  have hnGap : scale * target ≤ gap * F.n k := by
    calc
      scale * target ≤ F.n k := hn
      _ ≤ gap * F.n k := by
        have : 1 ≤ gap := hgap
        nlinarith
  have hdense : gap * F.n k ≤ scale * F.r k := by
    simpa [gap, scale, Nat.mul_assoc] using F.matching_dense k
  exact Nat.le_of_mul_le_mul_left (hnGap.trans hdense) hscale

variable {B : SimpleProperBlueprint}

theorem matchingSize_le_playerPartSize
    (F : DenseERSSequence B.C) (k : ℕ) (p : Fin B.P)
    (hp : (B.E p).Nonempty) :
    F.r k ≤ playerPartSize B (F.r k) (F.t k) p := by
  have hE : 1 ≤ (B.E p).card := Finset.card_pos.mpr hp
  have hsuffix : 1 ≤ Fintype.card (SuffixIndexTuple B (F.t k) p) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ ↦ ⟨0, (F.host k).t_pos⟩⟩
  have hrPow : F.r k ≤ (F.r k) ^ B.P := by
    simpa using Nat.pow_le_pow_right (F.host k).r_pos B.hP
  unfold playerPartSize
  calc
    F.r k ≤ (F.r k) ^ B.P := hrPow
    _ ≤ (B.E p).card * (F.r k) ^ B.P :=
      Nat.le_mul_of_pos_left _ hE
    _ ≤ Fintype.card (SuffixIndexTuple B (F.t k) p) *
        ((B.E p).card * (F.r k) ^ B.P) :=
      Nat.le_mul_of_pos_left _ hsuffix

theorem eventually_playerPartSize_ge
    (F : DenseERSSequence B.C) (target : ℕ) :
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ p : Fin B.P,
      (B.E p).Nonempty →
        target ≤ playerPartSize B (F.r k) (F.t k) p := by
  obtain ⟨k₀, hk₀⟩ := F.matchingSizesTendToInfinity target
  refine ⟨k₀, fun k hk p hp ↦ ?_⟩
  exact (hk₀ k hk).trans (F.matchingSize_le_playerPartSize k p hp)

theorem expansionSideSizesTendToInfinity
    (F : DenseERSSequence B.C) :
    SizesTendToInfinity (fun k ↦ (F.n k) ^ B.P) := by
  intro target
  obtain ⟨k₀, hk₀⟩ := F.baseSizesGrow (max target 1)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hn := hk₀ k hk
  have htarget : target ≤ F.n k :=
    (le_max_left target 1).trans hn
  have hnpos : 0 < F.n k := lt_of_lt_of_le (by omega) hn
  exact htarget.trans (by
    simpa using Nat.pow_le_pow_right hnpos B.hP)

theorem eventually_multiplicity_ge
    (F : DenseERSSequence B.C) (constant : ℕ) :
    ∃ k₀, ∀ k, k₀ ≤ k → constant ≤ F.t k := by
  obtain ⟨k₀, hk₀⟩ := F.multiplicityGrowth B.P B.hP constant 0
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simpa using hk₀ k hk

theorem playerPartSizesTendToInfinity
    (F : DenseERSSequence B.C) (p : Fin B.P) (hp : (B.E p).Nonempty) :
    SizesTendToInfinity (fun k ↦ playerPartSize B (F.r k) (F.t k) p) := by
  intro target
  obtain ⟨k0, hk0⟩ := F.matchingSizesTendToInfinity target
  refine ⟨k0, fun k hk ↦ ?_⟩
  have hrTarget : target ≤ F.r k := hk0 k hk
  exact hrTarget.trans (F.matchingSize_le_playerPartSize k p hp)

end DenseERSSequence

end ERSFamily

end Formal.Streaming
