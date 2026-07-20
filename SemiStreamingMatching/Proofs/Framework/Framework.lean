import SemiStreamingMatching.Proofs.Framework.BlueprintRatio
import SemiStreamingMatching.Definitions.SemiStreaming
import SemiStreamingMatching.Proofs.Framework.StreamingReduction

namespace Formal.Streaming

structure BlueprintHardFamily (B : SimpleProperBlueprint) where
  hostMultiplicity : ℕ → ℕ
  distribution :
    (n : ℕ) → FinitePartitionDistribution (B.P + 1) (Fin n) (Fin n)
  approximation : ℚ
  successThreshold : ℚ
  communicationScale : ℕ
  multiplicityGrowth : DominatesPolylog hostMultiplicity
  communicationHard :
    ∀ n s, communicationScale * s ≤ n * hostMultiplicity n →
      (distribution n).IsHardForCommunication approximation successThreshold s

namespace BlueprintHardFamily

theorem defeats_semiStreaming
    {B : SimpleProperBlueprint} (F : BlueprintHardFamily B)
    (A : SemiStreamingAlgorithm) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ x : (F.distribution n).Sample,
        (A.algorithm n).successProbability F.approximation
            ((F.distribution n).input x).graph
            ((F.distribution n).input x).stream ≤ F.successThreshold := by
  obtain ⟨n₀, hspace⟩ := semiStreaming_eventually_le_n_mul
    A.semiStreamingSpace F.multiplicityGrowth F.communicationScale
  refine ⟨n₀, fun n hn ↦ ?_⟩
  exact (F.distribution n).proposition_2_1
    (F.communicationHard n (A.spaceBits n) (hspace n hn))
    (A.algorithm n) (A.usesBits n)

def HasPaperParameters (F : BlueprintHardFamily B) (ε : ℚ) : Prop :=
  F.approximation = blueprintRatioRat B + ε ∧
    F.successThreshold = 1 - ε

theorem paper_lower_bound
    {B : SimpleProperBlueprint} {ε : ℚ}
    (F : BlueprintHardFamily B) (hF : F.HasPaperParameters ε)
    (A : SemiStreamingAlgorithm) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ x : (F.distribution n).Sample,
        (A.algorithm n).successProbability (blueprintRatioRat B + ε)
            ((F.distribution n).input x).graph
            ((F.distribution n).input x).stream ≤ 1 - ε := by
  rcases hF with ⟨hratio, hsuccess⟩
  simpa [hratio, hsuccess] using F.defeats_semiStreaming A

end BlueprintHardFamily

structure SequentialBlueprintHardFamily (B : SimpleProperBlueprint) where
  size : ℕ → ℕ
  hostMultiplicity : ℕ → ℕ
  distribution :
    (k : ℕ) → FinitePartitionDistribution (B.P + 1) (Fin (size k)) (Fin (size k))
  approximation : ℚ
  successThreshold : ℚ
  communicationScale : ℕ
  spaceDomination :
    ∀ space : ℕ → ℕ, IsSemiStreamingSpace space →
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
        communicationScale * space (size k) ≤ size k * hostMultiplicity k
  communicationHard :
    ∀ k s, communicationScale * s ≤ size k * hostMultiplicity k →
      (distribution k).IsHardForCommunication approximation successThreshold s

namespace SequentialBlueprintHardFamily

def HasPaperParameters (F : SequentialBlueprintHardFamily B) (ε : ℚ) : Prop :=
  F.approximation = blueprintRatioRat B + ε ∧
    F.successThreshold = 1 - ε

theorem defeats_semiStreaming
    {B : SimpleProperBlueprint} (F : SequentialBlueprintHardFamily B)
    (A : SemiStreamingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.distribution k).Sample,
        (A.algorithm (F.size k)).successProbability F.approximation
            ((F.distribution k).input x).graph
            ((F.distribution k).input x).stream ≤ F.successThreshold := by
  obtain ⟨k₀, hspace⟩ := F.spaceDomination A.spaceBits A.semiStreamingSpace
  refine ⟨k₀, fun k hk ↦ ?_⟩
  exact (F.distribution k).proposition_2_1
    (F.communicationHard k (A.spaceBits (F.size k)) (hspace k hk))
    (A.algorithm (F.size k)) (A.usesBits (F.size k))

theorem blueprint_to_semiStreaming_lower_bound
    {B : SimpleProperBlueprint} {ε : ℚ}
    (F : SequentialBlueprintHardFamily B) (hF : F.HasPaperParameters ε)
    (A : SemiStreamingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.distribution k).Sample,
        (A.algorithm (F.size k)).successProbability (blueprintRatioRat B + ε)
            ((F.distribution k).input x).graph
            ((F.distribution k).input x).stream ≤ 1 - ε := by
  rcases hF with ⟨hratio, hsuccess⟩
  simpa [hratio, hsuccess] using F.defeats_semiStreaming A

end SequentialBlueprintHardFamily

end Formal.Streaming
