import SemiStreamingMatching.Definitions.Algorithm
import SemiStreamingMatching.Definitions.Asymptotics

namespace Formal.Streaming

structure SemiStreamingAlgorithm where
  algorithm : (n : ℕ) → RandomizedOnePassAlgorithm (Fin n) (Fin n)
  spaceBits : ℕ → ℕ
  usesBits : ∀ n, (algorithm n).UsesBits (spaceBits n)
  semiStreamingSpace : IsSemiStreamingSpace spaceBits

namespace SemiStreamingAlgorithm

noncomputable def successProbability (A : SemiStreamingAlgorithm)
    {n : ℕ} (ρ : ℚ) (G : BipartiteGraph (Fin n) (Fin n))
    (σ : G.EdgeStream) : ℚ :=
  (A.algorithm n).successProbability ρ G σ

def FailsAt (A : SemiStreamingAlgorithm) (n : ℕ) (ρ p : ℚ) : Prop :=
  ∃ (G : BipartiteGraph (Fin n) (Fin n)) (σ : G.EdgeStream),
    A.successProbability ρ G σ < p

def SucceedsAt (A : SemiStreamingAlgorithm) (n : ℕ) (ρ p : ℚ) : Prop :=
  ∀ (G : BipartiteGraph (Fin n) (Fin n)) (σ : G.EdgeStream),
    p ≤ A.successProbability ρ G σ

theorem failsAt_iff_not_succeedsAt (A : SemiStreamingAlgorithm)
    (n : ℕ) (ρ p : ℚ) :
    A.FailsAt n ρ p ↔ ¬ A.SucceedsAt n ρ p := by
  simp only [FailsAt, SucceedsAt, not_forall, not_le]

end SemiStreamingAlgorithm

end Formal.Streaming
