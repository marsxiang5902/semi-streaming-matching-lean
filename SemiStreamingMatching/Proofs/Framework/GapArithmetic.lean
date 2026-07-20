import SemiStreamingMatching.Proofs.Framework.Augmentation
import SemiStreamingMatching.Proofs.Framework.BlueprintRatio

namespace Formal.Streaming

theorem normalized_matching_gap_lt
    {v x a dLoss qLoss eta epsilon : ℚ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha0 : 0 ≤ a) (hd0 : 0 ≤ dLoss) (hq0 : 0 ≤ qLoss)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : v - a ≤ x) (hxUpper : x ≤ v + a)
    (hNumeratorError : 2 * a + qLoss ≤ eta)
    (hDenominatorError : a + dLoss ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    2 - 2 * x + qLoss <
      ((2 - 2 * v) / (2 - v) + epsilon) * (2 - x - dLoss) := by
  have hBaseDenPos : 0 < 2 - v - eta := by linarith
  have hActualDenLower : 2 - v - eta ≤ 2 - x - dLoss := by
    linarith
  have hActualDenPos : 0 < 2 - x - dLoss :=
    lt_of_lt_of_le hBaseDenPos hActualDenLower
  have hNumerator :
      2 - 2 * x + qLoss ≤ 2 - 2 * v + eta := by
    linarith
  have hEtaFromErrors : 0 ≤ eta := by
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ 2 by norm_num) ha0,
      add_nonneg (mul_nonneg (show (0 : ℚ) ≤ 2 by norm_num) ha0) hq0]
  have hPerturbed := perturbed_ratioRat_le hv0 hv1 hEtaFromErrors heta1
  have hBaseProduct :
      2 - 2 * v + eta ≤
        ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - v - eta) :=
    (div_le_iff hBaseDenPos).1 hPerturbed
  have hRatioNonneg : 0 ≤ (2 - 2 * v) / (2 - v) := by
    exact div_nonneg (by linarith) (by linarith)
  have hPerturbedNonneg :
      0 ≤ (2 - 2 * v) / (2 - v) + 8 * eta := by
    exact add_nonneg hRatioNonneg (mul_nonneg (by norm_num) heta0)
  have hDenominatorMonotone :
      ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - v - eta) ≤
        ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - x - dLoss) :=
    mul_le_mul_of_nonneg_left hActualDenLower hPerturbedNonneg
  have hThreshold :
      (2 - 2 * v) / (2 - v) + 8 * eta <
        (2 - 2 * v) / (2 - v) + epsilon := by
    linarith
  have hThresholdProduct :
      ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - x - dLoss) <
        ((2 - 2 * v) / (2 - v) + epsilon) * (2 - x - dLoss) :=
    mul_lt_mul_of_pos_right hThreshold hActualDenPos
  calc
    2 - 2 * x + qLoss ≤ 2 - 2 * v + eta := hNumerator
    _ ≤ ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - v - eta) :=
      hBaseProduct
    _ ≤ ((2 - 2 * v) / (2 - v) + 8 * eta) * (2 - x - dLoss) :=
      hDenominatorMonotone
    _ < ((2 - 2 * v) / (2 - v) + epsilon) * (2 - x - dLoss) :=
      hThresholdProduct

theorem blueprint_normalized_matching_gap_lt
    (B : SimpleProperBlueprint) {x a dLoss qLoss eta epsilon : ℚ}
    (ha0 : 0 ≤ a) (hd0 : 0 ≤ dLoss) (hq0 : 0 ≤ qLoss)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : blueprintValueRat B - a ≤ x)
    (hxUpper : x ≤ blueprintValueRat B + a)
    (hNumeratorError : 2 * a + qLoss ≤ eta)
    (hDenominatorError : a + dLoss ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    2 - 2 * x + qLoss <
      (blueprintRatioRat B + epsilon) * (2 - x - dLoss) := by
  simpa only [blueprintRatioRat] using
    normalized_matching_gap_lt
      (blueprintValueRat_nonneg B) (blueprintValueRat_le_one B)
      ha0 hd0 hq0 heta0 heta1 hxLower hxUpper hNumeratorError
      hDenominatorError hSlack

theorem nat_matching_gap_lt
    {v a eta epsilon : ℚ} {N m d q : ℕ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hN : 0 < N) (hm : m ≤ N) (hmd : m + d ≤ 2 * N)
    (ha0 : 0 ≤ a) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : v - a ≤ (m : ℚ) / N)
    (hxUpper : (m : ℚ) / N ≤ v + a)
    (hNumeratorError : 2 * a + (q : ℚ) / N ≤ eta)
    (hDenominatorError : a + (d : ℚ) / N ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    ((((N - m) + (N - m) + q : ℕ) : ℚ)) <
      ((2 - 2 * v) / (2 - v) + epsilon) *
        (((2 * N - m - d : ℕ) : ℚ)) := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hNorm := normalized_matching_gap_lt hv0 hv1 ha0
    (div_nonneg (Nat.cast_nonneg _) hNq.le)
    (div_nonneg (Nat.cast_nonneg _) hNq.le)
    heta0 heta1 hxLower hxUpper hNumeratorError hDenominatorError hSlack
  have hmTwo : m ≤ 2 * N := by omega
  have hdSub : d ≤ 2 * N - m := by omega
  have hOrdinaryNormalize :
      ((((N - m) + (N - m) + q : ℕ) : ℚ)) / N =
        2 - 2 * ((m : ℚ) / N) + (q : ℚ) / N := by
    push_cast [Nat.cast_sub hm]
    field_simp
    ring
  have hOptimumNormalize :
      (((2 * N - m - d : ℕ) : ℚ)) / N =
        2 - (m : ℚ) / N - (d : ℚ) / N := by
    rw [Nat.cast_sub hdSub, Nat.cast_sub hmTwo]
    push_cast
    field_simp
  have hDivided :
      ((((N - m) + (N - m) + q : ℕ) : ℚ)) / N <
        ((2 - 2 * v) / (2 - v) + epsilon) *
          ((((2 * N - m - d : ℕ) : ℚ)) / N) := by
    rw [hOrdinaryNormalize, hOptimumNormalize]
    exact hNorm
  calc
    ((((N - m) + (N - m) + q : ℕ) : ℚ)) =
        (((((N - m) + (N - m) + q : ℕ) : ℚ)) / N) * N := by
          field_simp
    _ < (((2 - 2 * v) / (2 - v) + epsilon) *
          ((((2 * N - m - d : ℕ) : ℚ)) / N)) * N :=
      mul_lt_mul_of_pos_right hDivided hNq
    _ = ((2 - 2 * v) / (2 - v) + epsilon) *
          (((2 * N - m - d : ℕ) : ℚ)) := by
      field_simp

theorem blueprint_nat_matching_gap_lt
    (B : SimpleProperBlueprint) {a eta epsilon : ℚ} {N m d q : ℕ}
    (hN : 0 < N) (hm : m ≤ N) (hmd : m + d ≤ 2 * N)
    (ha0 : 0 ≤ a) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : blueprintValueRat B - a ≤ (m : ℚ) / N)
    (hxUpper : (m : ℚ) / N ≤ blueprintValueRat B + a)
    (hNumeratorError : 2 * a + (q : ℚ) / N ≤ eta)
    (hDenominatorError : a + (d : ℚ) / N ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    ((((N - m) + (N - m) + q : ℕ) : ℚ)) <
      (blueprintRatioRat B + epsilon) *
        (((2 * N - m - d : ℕ) : ℚ)) := by
  simpa only [blueprintRatioRat] using nat_matching_gap_lt
    (blueprintValueRat_nonneg B) (blueprintValueRat_le_one B)
    hN hm hmd ha0 heta0 heta1 hxLower hxUpper hNumeratorError
    hDenominatorError hSlack

theorem blueprint_vertexCount_eq_pow (B : SimpleProperBlueprint) :
    B.vertexCount = B.C ^ B.P := by
  classical
  simp [SimpleProperBlueprint.vertexCount, Vertex, Fintype.card_pi]

namespace ERSGraph

variable {L R : Type*} {C r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem left_card_pos (H : ERSGraph L R C r t) : 0 < Fintype.card L := by
  let i : Fin t := ⟨0, H.t_pos⟩
  let x : Fin C := ⟨0, H.C_pos⟩
  have hle := Finset.card_le_card
    (Finset.subset_univ (BipartiteGraph.leftEndpoints (H.matching i x x)))
  rw [BipartiteGraph.leftEndpoints_card_of_isMatching
    (H.matching_isMatching i x x), H.matching_card] at hle
  exact H.r_pos.trans_le hle

end ERSGraph

namespace SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem canonical_density_eq (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    ((canonicalMatching B H J).card : ℚ) /
        Fintype.card (Left B L) =
      ((B.edgeCount * r ^ B.P : ℕ) : ℚ) /
        ((Fintype.card L) ^ B.P : ℕ) := by
  rw [canonicalMatching_card, expansion_left_card]

theorem canonical_density_eq_blueprintValue_mul (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    ((canonicalMatching B H J).card : ℚ) /
        Fintype.card (Left B L) =
      blueprintValueRat B *
        ((((r : ℚ) * B.C) / Fintype.card L) ^ B.P) := by
  rw [canonical_density_eq, blueprintValueRat, blueprint_vertexCount_eq_pow]
  push_cast
  have hC : (B.C : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt B.hC)
  have hL : ((Fintype.card L : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt H.left_card_pos)
  field_simp
  ring

end SimpleExpansion

namespace AugmentedExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem matchingGapCertificate_gap
    {B : SimpleProperBlueprint}
    {G0 : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G0.IsMatching canonical)
    (hside : Fintype.card (BaseLeft (L := L) B) =
      Fintype.card (BaseRight (R := R) B))
    {d q : ℕ} (hdeleted : (canonical \ kept).card ≤ d)
    {a eta epsilon : ℚ}
    (hN : 0 < Fintype.card (BaseLeft (L := L) B))
    (hmd : canonical.card + d ≤
      2 * Fintype.card (BaseLeft (L := L) B))
    (ha0 : 0 ≤ a) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : blueprintValueRat B - a ≤
      (canonical.card : ℚ) / Fintype.card (BaseLeft (L := L) B))
    (hxUpper : (canonical.card : ℚ) /
      Fintype.card (BaseLeft (L := L) B) ≤ blueprintValueRat B + a)
    (hNumeratorError : 2 * a + (q : ℚ) /
      Fintype.card (BaseLeft (L := L) B) ≤ eta)
    (hDenominatorError : a + (d : ℚ) /
      Fintype.card (BaseLeft (L := L) B) ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    (((matchingGapCertificate hcanonical hside d hdeleted).ordinaryUpper + q : ℕ) : ℚ) <
      (blueprintRatioRat B + epsilon) *
        (matchingGapCertificate hcanonical hside d hdeleted).optimumLower := by
  have hm : canonical.card ≤ Fintype.card (BaseLeft (L := L) B) := by
    have hle := Finset.card_le_card
      (Finset.subset_univ (BipartiteGraph.leftEndpoints canonical))
    rw [BipartiteGraph.leftEndpoints_card_of_isMatching hcanonical] at hle
    exact hle
  change
    ((((Fintype.card (BaseLeft (L := L) B) - canonical.card) +
      (Fintype.card (BaseRight (R := R) B) - canonical.card) + q : ℕ) : ℚ)) <
      (blueprintRatioRat B + epsilon) *
        (((2 * Fintype.card (BaseLeft (L := L) B) - canonical.card - d : ℕ) : ℚ))
  rw [← hside]
  exact blueprint_nat_matching_gap_lt B hN hm hmd ha0 heta0 heta1
    hxLower hxUpper hNumeratorError hDenominatorError hSlack

theorem expansion_matchingGapCertificate_gap
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : SimpleExpansion.IndexTuple B t)
    {kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {d q : ℕ}
    (hdeleted : (SimpleExpansion.canonicalMatching B H J \ kept).card ≤ d)
    {a eta epsilon : ℚ}
    (hmd : B.edgeCount * r ^ B.P + d ≤
      2 * (Fintype.card L) ^ B.P)
    (ha0 : 0 ≤ a) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : blueprintValueRat B - a ≤
      ((B.edgeCount * r ^ B.P : ℕ) : ℚ) /
        ((Fintype.card L) ^ B.P : ℕ))
    (hxUpper : ((B.edgeCount * r ^ B.P : ℕ) : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ blueprintValueRat B + a)
    (hNumeratorError : 2 * a + (q : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ eta)
    (hDenominatorError : a + (d : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    (((matchingGapCertificate
      (SimpleExpansion.canonicalMatching_isMatching B H J)
      (SimpleExpansion.expansion_side_card_eq B H) d hdeleted).ordinaryUpper + q : ℕ) : ℚ) <
      (blueprintRatioRat B + epsilon) *
        (matchingGapCertificate
          (SimpleExpansion.canonicalMatching_isMatching B H J)
          (SimpleExpansion.expansion_side_card_eq B H) d hdeleted).optimumLower := by
  apply matchingGapCertificate_gap
    (SimpleExpansion.canonicalMatching_isMatching B H J)
    (SimpleExpansion.expansion_side_card_eq B H) hdeleted
  · rw [SimpleExpansion.expansion_left_card]
    exact Nat.pow_pos H.left_card_pos
  · simpa only [SimpleExpansion.canonicalMatching_card,
      SimpleExpansion.expansion_left_card] using hmd
  · exact ha0
  · exact heta0
  · exact heta1
  · simpa only [SimpleExpansion.canonicalMatching_card,
      SimpleExpansion.expansion_left_card] using hxLower
  · simpa only [SimpleExpansion.canonicalMatching_card,
      SimpleExpansion.expansion_left_card] using hxUpper
  · simpa only [SimpleExpansion.expansion_left_card] using hNumeratorError
  · simpa only [SimpleExpansion.expansion_left_card] using hDenominatorError
  · exact hSlack

end AugmentedExpansion

end Formal.Streaming
