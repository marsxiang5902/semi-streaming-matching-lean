import SemiStreamingMatching.Proofs.Framework.ERS
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSGraph

variable {L R : Type*} {C r t : ℕ}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem row_card (H : ERSGraph L R C r t) (i : Fin t) (x : Fin C) :
    (Finset.univ.biUnion fun y ↦ H.matching i x y).card = C * r := by
  rw [Finset.card_biUnion]
  · simp [H.matching_card]
  · intro y _hy y' _hy' hyy'
    exact H.labelled_matchings_disjoint (by
      intro hpair
      exact hyy' (congrArg Prod.snd hpair))

theorem matchingGroup_card (H : ERSGraph L R C r t) (i : Fin t) :
    (H.matchingGroup i).card = C * C * r := by
  unfold matchingGroup matchingGroupOf
  rw [Finset.card_biUnion]
  · simp_rw [H.row_card]
    simp
    ring
  · intro x _hx x' _hx' hxx'
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he he'
    obtain ⟨y, hey⟩ := he
    obtain ⟨y', hey'⟩ := he'
    exact Finset.disjoint_left.mp
      (H.labelled_matchings_disjoint (by
        intro hpair
        exact hxx' (congrArg Prod.fst hpair))) hey hey'

def allMatchingGroups (H : ERSGraph L R C r t) :
    Finset (Formal.Streaming.Edge L R) :=
  Finset.univ.biUnion H.matchingGroup

theorem allMatchingGroups_card (H : ERSGraph L R C r t) :
    H.allMatchingGroups.card = t * (C * C * r) := by
  unfold allMatchingGroups
  rw [Finset.card_biUnion]
  · simp_rw [H.matchingGroup_card]
    simp
  · intro i _hi j _hj hij
    exact H.matchingGroup_disjoint hij

theorem allMatchingGroups_subset_graph (H : ERSGraph L R C r t) :
    H.allMatchingGroups ⊆ H.graph.edges := by
  intro e he
  simp only [allMatchingGroups, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at he
  obtain ⟨i, hei⟩ := he
  exact H.matchingGroup_subset_graph i hei

theorem multiplicity_mul_matchingGroup_card_le (H : ERSGraph L R C r t) :
    t * (C * C * r) ≤ Fintype.card L * Fintype.card R := by
  rw [← H.allMatchingGroups_card]
  calc
    H.allMatchingGroups.card ≤ H.graph.edges.card :=
      Finset.card_le_card H.allMatchingGroups_subset_graph
    _ ≤ (Finset.univ : Finset (Formal.Streaming.Edge L R)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card L * Fintype.card R := by simp [Fintype.card_prod]

theorem multiplicity_le_side_sq (H : ERSGraph L R C r t) :
    t ≤ Fintype.card L ^ 2 := by
  have hfactor : 1 ≤ C * C * r := by
    have hC : 1 ≤ C := H.C_pos
    have hr : 1 ≤ r := H.r_pos
    nlinarith
  have ht : t ≤ t * (C * C * r) := by
    simpa using Nat.mul_le_mul_left t hfactor
  calc
    t ≤ t * (C * C * r) := ht
    _ ≤ Fintype.card L * Fintype.card R :=
      H.multiplicity_mul_matchingGroup_card_le
    _ = Fintype.card L ^ 2 := by rw [← H.side_card_eq]; ring

end ERSGraph

end Formal.Streaming
