import SemiStreamingMatching.Proofs.Framework.DeletionParameters
import SemiStreamingMatching.Proofs.Framework.ERSCardinality
import SemiStreamingMatching.Proofs.Framework.ERSDensity
import Mathlib.Tactic

namespace Formal.Streaming

namespace HardDistribution

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem suffixIndexTuple_card_le_pow_P
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (p : Fin B.P) :
    Fintype.card (SuffixIndexTuple B t p) ≤ t ^ B.P := by
  rw [suffixIndexTuple_card]
  have hsuffix : Fintype.card (SuffixCoordinates B p) ≤ B.P := by
    simpa using (Fintype.card_subtype_le fun q : Fin B.P ↦ p ≤ q)
  exact Nat.pow_le_pow_right H.t_pos hsuffix

theorem blueprintPart_card_le_vertex_sq
    (B : SimpleProperBlueprint) (p : Fin B.P) :
    (B.E p).card ≤ (B.C ^ B.P) ^ 2 := by
  calc
    (B.E p).card ≤ (Finset.univ : Finset (_root_.Edge B.P B.C)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (_root_.Edge B.P B.C) := Finset.card_univ
    _ = (B.C ^ B.P) ^ 2 := by
      simp [Vertex, _root_.Edge, Fintype.card_pi, pow_two]

theorem colorCount_le_side_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t) :
    B.C ≤ Fintype.card L := by
  have hCr := H.matching_density_le_card
  have hC : B.C ≤ B.C * r := by
    simpa using Nat.mul_le_mul_left B.C H.r_pos
  exact hC.trans hCr

theorem matchingSize_le_side_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t) :
    r ≤ Fintype.card L := by
  have hr : r ≤ B.C * r := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left r H.C_pos
  exact hr.trans H.matching_density_le_card

theorem playerPartSize_le_side_pow
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (p : Fin B.P) :
    playerPartSize B r t p ≤ (Fintype.card L) ^ (5 * B.P) := by
  let n := Fintype.card L
  have hsuffix : Fintype.card (SuffixIndexTuple B t p) ≤ t ^ B.P :=
    suffixIndexTuple_card_le_pow_P B H p
  have ht : t ≤ n ^ 2 := by
    simpa [n] using H.multiplicity_le_side_sq
  have hsuffixN : Fintype.card (SuffixIndexTuple B t p) ≤ n ^ (2 * B.P) := by
    calc
      Fintype.card (SuffixIndexTuple B t p) ≤ t ^ B.P := hsuffix
      _ ≤ (n ^ 2) ^ B.P := Nat.pow_le_pow_left ht _
      _ = n ^ (2 * B.P) := by rw [← pow_mul]
  have hE : (B.E p).card ≤ n ^ (2 * B.P) := by
    calc
      (B.E p).card ≤ (B.C ^ B.P) ^ 2 := blueprintPart_card_le_vertex_sq B p
      _ ≤ (n ^ B.P) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (colorCount_le_side_card B H) _) _
      _ = n ^ (2 * B.P) := by
        rw [← pow_mul]
        congr 1
        omega
  have hr : r ^ B.P ≤ n ^ B.P :=
    Nat.pow_le_pow_left (matchingSize_le_side_card B H) _
  unfold playerPartSize
  calc
    Fintype.card (SuffixIndexTuple B t p) * ((B.E p).card * r ^ B.P) ≤
        n ^ (2 * B.P) * (n ^ (2 * B.P) * n ^ B.P) := by
      gcongr
    _ = n ^ (5 * B.P) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

theorem playerEdge_card_le_side_pow
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) :
    Fintype.card
        {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} ≤
      (Fintype.card L) ^ (5 * B.P) := by
  rw [Fintype.card_coe, ← playerPartSize_eq_part_card B H J p]
  exact playerPartSize_le_side_pow B H p

theorem playerEdge_log_succ_le_five_log_augmented
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) :
    Real.log (Fintype.card
          {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} + 1) ≤
      5 * Real.log (2 * (Fintype.card L) ^ B.P) := by
  let n := Fintype.card L
  let mLocal := Fintype.card
    {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p}
  let augmented := 2 * n ^ B.P
  have hnpos : 0 < n := H.left_card_pos
  have hlocal : mLocal ≤ n ^ (5 * B.P) := by
    simpa [mLocal, n] using playerEdge_card_le_side_pow B H J p
  have hpow : n ^ (5 * B.P) = (n ^ B.P) ^ 5 := by
    rw [← pow_mul]
    congr 1
    omega
  have hnat : mLocal + 1 ≤ augmented ^ 5 := by
    rw [hpow] at hlocal
    change mLocal + 1 ≤ (2 * n ^ B.P) ^ 5
    calc
      mLocal + 1 ≤ (n ^ B.P) ^ 5 + 1 := Nat.add_le_add_right hlocal 1
      _ ≤ 2 * (n ^ B.P) ^ 5 := by
        have : 1 ≤ (n ^ B.P) ^ 5 :=
          Nat.one_le_pow 5 (n ^ B.P) (Nat.pow_pos hnpos)
        omega
      _ ≤ (2 * n ^ B.P) ^ 5 := by
        ring_nf
        omega
  have hlocalPos : (0 : ℝ) < mLocal + 1 := by positivity
  have haugPos : (0 : ℝ) < augmented ^ 5 := by
    have : 0 < augmented := by positivity
    positivity
  have hlog : Real.log (mLocal + 1) ≤ Real.log (augmented ^ 5) :=
    (Real.log_le_log_iff hlocalPos haugPos).2 (by exact_mod_cast hnat)
  rw [Real.log_pow] at hlog
  simpa [mLocal, augmented, n, Nat.cast_ofNat] using hlog

end HardDistribution

end Formal.Streaming
