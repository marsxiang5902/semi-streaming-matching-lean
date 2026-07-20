import SemiStreamingMatching.Proofs.GreedyOptimalCommon

open Formal.Streaming

namespace SemiStreamingMatching

theorem no_semiStreaming_beats_half {δ ε : ℚ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ size : ℕ → ℕ, SizesTendToInfinity size ∧
      ∀ A : SemiStreamingMatchingAlgorithm, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
        ∃ (G : BipartiteGraph (Fin (size k)) (Fin (size k))) (σ : G.EdgeStream),
          A.successProbability (1 / 2 + δ) G σ ≤ ε := by
  set s : ℚ := δ / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  obtain ⟨B, hbrQ⟩ := exists_blueprint_ratio_lt_half_add hδ hδ'
  have hle : blueprintRatioRat B + s ≤ 1 / 2 + δ := by rw [hsdef]; linarith
  obtain ⟨Dd, hDd, happrox⟩ :=
    Formal.Streaming.ERSFamily.DenseERSSequence.exists_reciprocal_denominator hs
  obtain ⟨F, hloss, hbase, ht, hactive⟩ :=
    Formal.Streaming.ERSFamily.DenseERSSequence.exists_reciprocal_tail B Dd hDd
  refine ⟨F.augmentedExpansionSize B.P, F.augmentedSizesTendToInfinity B.hP, ?_⟩
  intro A
  obtain ⟨k₀, hk₀⟩ :=
    F.reciprocal_tail_defeats_general Dd hDd hloss hbase
      (fun k bits hbits =>
        F.reciprocal_exactRecoverableSpecialSumBound hDd k bits (hactive k) (ht k) hbits)
      happrox hε0 hε1 A
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨x, hx⟩ := hk₀ k hk
  exact ⟨_, _, le_trans (successProbability_antitone _ _ _ hle) hx⟩

end SemiStreamingMatching
