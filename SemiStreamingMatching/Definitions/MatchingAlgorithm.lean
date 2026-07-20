import SemiStreamingMatching.Definitions.SemiStreaming

namespace Formal.Streaming

namespace RandomizedOnePassAlgorithm

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def AlwaysFeasible (A : RandomizedOnePassAlgorithm L R) : Prop :=
  ∀ (ξ : A.Seed) (G : BipartiteGraph L R) (σ : G.EdgeStream),
    G.IsMatching ((A.fixSeed ξ).result σ.order)

end RandomizedOnePassAlgorithm

structure SemiStreamingMatchingAlgorithm extends SemiStreamingAlgorithm where
  alwaysFeasible : ∀ n, (algorithm n).AlwaysFeasible

end Formal.Streaming
