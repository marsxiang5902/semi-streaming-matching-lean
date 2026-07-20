import SemiStreamingMatching.Proofs.Blueprint.Results
import SemiStreamingMatching.Proofs.Framework

open Formal.Streaming

namespace SemiStreamingMatching

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem successProbability_antitone
    (A : RandomizedOnePassAlgorithm L R)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) {ρ ρ' : ℚ} (h : ρ' ≤ ρ) :
    A.successProbability ρ G σ ≤ A.successProbability ρ' G σ := by
  have hsub : A.successfulSeeds ρ G σ ⊆ A.successfulSeeds ρ' G σ := by
    intro ξ hξ
    simp only [RandomizedOnePassAlgorithm.successfulSeeds, Finset.mem_filter,
      Formal.Streaming.OnePassAlgorithm.SucceedsOn,
      Formal.Streaming.OnePassAlgorithm.MeetsApproximation] at hξ ⊢
    obtain ⟨hmem, hM, hcard⟩ := hξ
    refine ⟨hmem, hM, ?_⟩
    calc ρ' * (G.matchingNumber : ℚ)
        ≤ ρ * (G.matchingNumber : ℚ) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ ≤ _ := hcard
  have hN : (0 : ℚ) < (Fintype.card A.Seed : ℚ) := by exact_mod_cast Fintype.card_pos
  unfold RandomizedOnePassAlgorithm.successProbability
  apply (div_le_div_right hN).2
  exact_mod_cast Finset.card_le_card hsub

theorem exists_blueprint_ratio_lt_half_add {δ : ℚ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ B : SimpleProperBlueprint, blueprintRatioRat B < 1 / 2 + δ / 2 := by
  set d : ℝ := (1 : ℝ) / 2 + (δ : ℝ) / 2 with hd
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδR1 : (δ : ℝ) ≤ 1 := by
    have : δ ≤ 1 := by linarith
    exact_mod_cast this
  have hdhalf : (1 : ℝ) < 2 * d := by rw [hd]; linarith
  have h2d : (0 : ℝ) < 2 - d := by rw [hd]; linarith
  have ht23 : (2 - 2 * d) / (2 - d) < 2 / 3 := by
    rw [div_lt_iff h2d]; nlinarith [hdhalf]
  obtain ⟨B, hBval⟩ :=
    exists_blueprint_value_near_two_thirds ((2 / 3 - (2 - 2 * d) / (2 - d)) / 2) (by linarith)
  refine ⟨B, ?_⟩
  have HK : 2 - 2 * d < B.value * (2 - d) := by
    have hvt : (2 - 2 * d) / (2 - d) < B.value := by
      have hrw : (2 : ℝ) / 3 - (2 / 3 - (2 - 2 * d) / (2 - d)) / 2
          = ((2 - 2 * d) / (2 - d) + 2 / 3) / 2 := by ring
      rw [hrw] at hBval; linarith
    exact (div_lt_iff h2d).1 hvt
  have hbr : blueprintRatio B < d := by
    rw [blueprintRatio, div_lt_iff (two_sub_value_pos B)]
    nlinarith [HK]
  have h : (blueprintRatioRat B : ℝ) < d := by rw [blueprintRatioRat_cast]; exact hbr
  rw [hd] at h
  have hcast : ((blueprintRatioRat B : ℚ) : ℝ) < ((1 / 2 + δ / 2 : ℚ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hcast

end SemiStreamingMatching
