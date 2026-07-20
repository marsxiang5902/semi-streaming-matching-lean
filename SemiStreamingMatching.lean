import SemiStreamingMatching.Definitions.Graph
import SemiStreamingMatching.Definitions.Algorithm
import SemiStreamingMatching.Definitions.Asymptotics
import SemiStreamingMatching.Definitions.SemiStreaming
import SemiStreamingMatching.Proofs.GreedyOptimal

open Formal.Streaming

theorem greedy_is_optimal {δ : ℚ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ (ε : ℚ) (size : ℕ → ℕ), 0 < ε ∧ SizesTendToInfinity size ∧
      ∀ A : SemiStreamingAlgorithm, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ (G : BipartiteGraph (Fin (size n)) (Fin (size n))) (σ : G.EdgeStream),
          A.successProbability (1 / 2 + δ) G σ ≤ 1 - ε :=
  SemiStreamingMatching.greedy_is_optimal hδ hδ'

#print axioms greedy_is_optimal
