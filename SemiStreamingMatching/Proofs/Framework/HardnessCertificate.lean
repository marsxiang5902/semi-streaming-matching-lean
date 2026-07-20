import SemiStreamingMatching.Definitions.Graph

namespace Formal.Streaming

open BipartiteGraph

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

structure MatchingGapCertificate (G : BipartiteGraph L R) where
  special : Finset (Edge L R)
  optimumLower : ℕ
  ordinaryUpper : ℕ
  optimumLower_le : optimumLower ≤ G.matchingNumber
  ordinary_part_le :
    ∀ ⦃M : Finset (Edge L R)⦄, G.IsMatching M →
      (M \ special).card ≤ ordinaryUpper

namespace MatchingGapCertificate

variable {G : BipartiteGraph L R}

theorem matching_card_le (cert : MatchingGapCertificate G)
    {M : Finset (Edge L R)} (hM : G.IsMatching M) {q : ℕ}
    (hspecial : (M ∩ cert.special).card ≤ q) :
    M.card ≤ cert.ordinaryUpper + q := by
  have hsplit : (M \ cert.special).card + (M ∩ cert.special).card = M.card := by
    rw [Finset.card_sdiff_add_card_inter]
  have hord := cert.ordinary_part_le hM
  omega

theorem not_approximation_of_few_special (cert : MatchingGapCertificate G)
    {M : Finset (Edge L R)} (hM : G.IsMatching M) {q : ℕ} {α : ℝ}
    (hspecial : (M ∩ cert.special).card ≤ q)
    (hgap : ((cert.ordinaryUpper + q : ℕ) : ℝ) < α * cert.optimumLower) :
    (M.card : ℝ) < α * G.matchingNumber := by
  have hcard := cert.matching_card_le hM hspecial
  have hopt : (cert.optimumLower : ℝ) ≤ G.matchingNumber := by
    exact_mod_cast cert.optimumLower_le
  have hα : 0 ≤ α := by
    by_contra hα
    have : α * (cert.optimumLower : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα) (Nat.cast_nonneg _)
    have : (0 : ℝ) < α * cert.optimumLower :=
      lt_of_le_of_lt (Nat.cast_nonneg _) hgap
    linarith
  calc
    (M.card : ℝ) ≤ cert.ordinaryUpper + q := by exact_mod_cast hcard
    _ < α * cert.optimumLower := by
      simpa only [Nat.cast_add] using hgap
    _ ≤ α * G.matchingNumber := mul_le_mul_of_nonneg_left hopt hα

end MatchingGapCertificate

end Formal.Streaming
