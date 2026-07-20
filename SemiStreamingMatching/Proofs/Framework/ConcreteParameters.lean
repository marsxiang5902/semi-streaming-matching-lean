import SemiStreamingMatching.Proofs.Framework.DenseGrowth
import SemiStreamingMatching.Proofs.Framework.HardDistributionCardinality
import SemiStreamingMatching.Proofs.Framework.SequenceTail
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

namespace DenseERSSequence

open HardDistribution SimpleExpansion

variable {B : SimpleProperBlueprint}

def baseExpansionSize (F : DenseERSSequence B.C) (k : ℕ) : ℕ :=
  (F.n k) ^ B.P

def reciprocalDeletions (F : DenseERSSequence B.C) (D k : ℕ) :
    Fin B.P → ℕ :=
  floorDeletionCount B (F.r k) (F.t k) 1 D

def reciprocalSpecialThreshold (F : DenseERSSequence B.C)
    (D k : ℕ) : ℕ :=
  F.baseExpansionSize k / D

def reciprocalDeletionAllowance (F : DenseERSSequence B.C)
    (D k : ℕ) : ℕ :=
  2 * (F.baseExpansionSize k / D) + 2

def reciprocalCommunicationScale (B : SimpleProperBlueprint) (D : ℕ) : ℕ :=
  2560 * D ^ 3 * B.P ^ 2

theorem exists_reciprocal_denominator {ε : ℚ} (hε : 0 < ε) :
    ∃ D : ℕ, 12 ≤ D ∧ (49 : ℚ) / D < ε := by
  obtain ⟨d, hd⟩ := exists_nat_gt ((49 : ℚ) / ε)
  let D := max 12 d
  have hD : 12 ≤ D := le_max_left _ _
  have hdD : (d : ℚ) ≤ D := by exact_mod_cast (le_max_right 12 d)
  have hratio : (49 : ℚ) / ε < D := hd.trans_le hdD
  have hDq : (0 : ℚ) < D := by exact_mod_cast (by omega : 0 < D)
  refine ⟨D, hD, (div_lt_iff hDq).2 ?_⟩
  exact (div_lt_iff hε).1 hratio |>.trans_eq (by ring)

theorem sixteen_mul_le_div_add_one_sq
    {D N : ℕ} (hD : 0 < D) (hlarge : 16 * D ^ 2 ≤ N) :
    16 * N ≤ (N / D + 1) ^ 2 := by
  have hquot : 16 * D ≤ N / D := by
    apply (Nat.le_div_iff_mul_le hD).2
    simpa [pow_two, Nat.mul_assoc] using hlarge
  have hupper := Nat.lt_mul_div_succ N hD
  calc
    16 * N ≤ 16 * (D * (N / D + 1)) :=
      Nat.mul_le_mul_left 16 hupper.le
    _ = (16 * D) * (N / D + 1) := by ring
    _ ≤ (N / D) * (N / D + 1) :=
      Nat.mul_le_mul_right (N / D + 1) hquot
    _ ≤ (N / D + 1) * (N / D + 1) :=
      Nat.mul_le_mul_right (N / D + 1) (Nat.le_succ (N / D))
    _ = (N / D + 1) ^ 2 := by ring

theorem baseExpansionSize_pos (F : DenseERSSequence B.C) (k : ℕ) :
    0 < F.baseExpansionSize k := by
  apply Nat.pow_pos
  simpa using (F.host k).left_card_pos

theorem canonicalSize_le_baseExpansionSize
    (F : DenseERSSequence B.C) (k : ℕ) :
    B.edgeCount * (F.r k) ^ B.P ≤ F.baseExpansionSize k := by
  let J : IndexTuple B (F.t k) := fun _ ↦ ⟨0, (F.host k).t_pos⟩
  have hmatching := canonicalMatching_isMatching B (F.host k) J
  have hcard := Finset.card_le_card
    (Finset.subset_univ (BipartiteGraph.leftEndpoints
      (canonicalMatching B (F.host k) J)))
  rw [BipartiteGraph.leftEndpoints_card_of_isMatching hmatching,
    canonicalMatching_card] at hcard
  simpa [Finset.card_univ, expansion_left_card, baseExpansionSize] using hcard

theorem reciprocalDeletions_admissible
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 1 ≤ D) (k : ℕ) :
    ∀ J p, F.reciprocalDeletions D k p ≤
      (part B (F.host k) J p).card := by
  exact floorDeletionCount_admissible B (F.host k) 1 D hD

theorem two_mul_reciprocalDeletions_le_part
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∀ J p, 2 * F.reciprocalDeletions D k p ≤
      (part B (F.host k) J p).card := by
  intro J p
  have hfloor := denominator_mul_floorDeletionCount_le
    B (F.r k) (F.t k) 1 D p
  rw [← playerPartSize_eq_part_card B (F.host k) J p]
  change 2 * floorDeletionCount B (F.r k) (F.t k) 1 D p ≤ _
  simpa only [one_mul] using (show
    2 * floorDeletionCount B (F.r k) (F.t k) 1 D p ≤
      playerPartSize B (F.r k) (F.t k) p by
        calc
          2 * floorDeletionCount B (F.r k) (F.t k) 1 D p ≤
              D * floorDeletionCount B (F.r k) (F.t k) 1 D p := by
            gcongr
          _ ≤ playerPartSize B (F.r k) (F.t k) p := by
            simpa only [one_mul] using hfloor)

theorem reciprocalDeletions_pos_of_part_ge
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (p : Fin B.P)
    (hpart : D ≤ playerPartSize B (F.r k) (F.t k) p) :
    0 < F.reciprocalDeletions D k p := by
  exact floorDeletionCount_pos B (F.r k) (F.t k) 1 D p hD
    (by simpa using hpart)

theorem blueprintPart_nonempty_of_playerPartSize_pos
    (F : DenseERSSequence B.C) (k : ℕ) (p : Fin B.P)
    (hpart : 0 < playerPartSize B (F.r k) (F.t k) p) :
    (B.E p).Nonempty := by
  apply Finset.card_pos.mp
  by_contra hE
  have hEzero : (B.E p).card = 0 := Nat.eq_zero_of_not_pos hE
  unfold playerPartSize at hpart
  simp [hEzero] at hpart

theorem reciprocalDeletions_pos_of_local_card_pos
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (hactive : ∀ p : Fin B.P, (B.E p).Nonempty →
      D ≤ playerPartSize B (F.r k) (F.t k) p)
    (J : IndexTuple B (F.t k)) (p : Fin B.P)
    (hlocal : 0 < Fintype.card
      {z : BaseEdge (L := Fin (F.n k)) (R := Fin (F.n k)) B //
        z ∈ part B (F.host k) J p}) :
    0 < F.reciprocalDeletions D k p := by
  have hpart : 0 < playerPartSize B (F.r k) (F.t k) p := by
    simpa only [Fintype.card_coe,
      playerPartSize_eq_part_card B (F.host k) J p] using hlocal
  exact F.reciprocalDeletions_pos_of_part_ge hD k p
    (hactive p (F.blueprintPart_nonempty_of_playerPartSize_pos k p hpart))

theorem reciprocalDeletions_pos_of_part_nonempty
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (hactive : ∀ p : Fin B.P, (B.E p).Nonempty →
      D ≤ playerPartSize B (F.r k) (F.t k) p)
    (J : IndexTuple B (F.t k)) (p : Fin B.P)
    (hpart : (part B (F.host k) J p).Nonempty) :
    0 < F.reciprocalDeletions D k p := by
  apply F.reciprocalDeletions_pos_of_local_card_pos hD k hactive J p
  rw [Fintype.card_coe]
  exact Finset.card_pos.mpr hpart

theorem local_card_eq_zero_of_reciprocalDeletions_eq_zero
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (hactive : ∀ p : Fin B.P, (B.E p).Nonempty →
      D ≤ playerPartSize B (F.r k) (F.t k) p)
    (J : IndexTuple B (F.t k)) (p : Fin B.P)
    (hq : F.reciprocalDeletions D k p = 0) :
    Fintype.card
      {z : BaseEdge (L := Fin (F.n k)) (R := Fin (F.n k)) B //
        z ∈ part B (F.host k) J p} = 0 := by
  by_contra hlocal
  have hpos := F.reciprocalDeletions_pos_of_local_card_pos hD k hactive J p
    (Nat.pos_of_ne_zero hlocal)
  omega

theorem reciprocalDeletions_real_rate_lower
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (J : IndexTuple B (F.t k)) (p : Fin B.P)
    (hq : 0 < F.reciprocalDeletions D k p) :
    (1 : ℝ) / (2 * D) ≤
      (F.reciprocalDeletions D k p : ℝ) /
        Fintype.card
          {z : BaseEdge (L := Fin (F.n k)) (R := Fin (F.n k)) B //
            z ∈ part B (F.host k) J p} := by
  let M := playerPartSize B (F.r k) (F.t k) p
  let q := floorDeletionCount B (F.r k) (F.t k) 1 D p
  have hupper :=
    numerator_mul_partSize_lt_denominator_mul_floorDeletionCount_add_one
      B (F.r k) (F.t k) 1 D p hD
  have hq' : 0 < q := by simpa [q, reciprocalDeletions] using hq
  have hMtwo : M ≤ q * (2 * D) := by
    dsimp [M, q]
    simp only [one_mul] at hupper
    nlinarith
  have hMpos : 0 < M := lt_of_lt_of_le hq' (by
    exact floorDeletionCount_le_playerPartSize
      B (F.r k) (F.t k) 1 D p (by omega))
  have hden : (0 : ℝ) < 2 * D := by positivity
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcross : (M : ℝ) ≤ (q : ℝ) * (2 * D) := by exact_mod_cast hMtwo
  rw [show Fintype.card
      {z : BaseEdge (L := Fin (F.n k)) (R := Fin (F.n k)) B //
        z ∈ part B (F.host k) J p} = M by
      simp only [Fintype.card_coe, M,
        playerPartSize_eq_part_card B (F.host k) J p]]
  change (1 : ℝ) / (2 * D) ≤ (q : ℝ) / M
  exact (div_le_div_iff hden hMreal).2 (by simpa using hcross)

theorem reciprocal_player_log_bound
    (F : DenseERSSequence B.C) (k : ℕ)
    (J : IndexTuple B (F.t k)) (p : Fin B.P) :
    Real.log (Fintype.card
          {z : BaseEdge (L := Fin (F.n k)) (R := Fin (F.n k)) B //
            z ∈ part B (F.host k) J p} + 1) ≤
      5 * Real.log (2 * F.baseExpansionSize k) := by
  simpa [baseExpansionSize] using
    playerEdge_log_succ_le_five_log_augmented B (F.host k) J p

theorem exists_uniform_tail_bounds
    (F : DenseERSSequence B.C)
    (baseTarget partTarget multiplicityTarget : ℕ) :
    ∃ offset, ∀ k,
      baseTarget ≤ F.baseExpansionSize (offset + k) ∧
      multiplicityTarget ≤ F.t (offset + k) ∧
      ∀ p : Fin B.P, (B.E p).Nonempty →
        partTarget ≤
          playerPartSize B (F.r (offset + k)) (F.t (offset + k)) p := by
  obtain ⟨kb, hkb⟩ := F.expansionSideSizesTendToInfinity baseTarget
  obtain ⟨kp, hkp⟩ := F.eventually_playerPartSize_ge partTarget
  obtain ⟨kt, hkt⟩ := F.eventually_multiplicity_ge multiplicityTarget
  refine ⟨max kb (max kp kt), fun k ↦ ?_⟩
  have hkb' : kb ≤ max kb (max kp kt) + k := by omega
  have hkp' : kp ≤ max kb (max kp kt) + k := by omega
  have hkt' : kt ≤ max kb (max kp kt) + k := by omega
  exact ⟨hkb _ hkb', hkt _ hkt', fun p hp ↦ hkp _ hkp' p hp⟩

theorem reciprocalSpecialThreshold_cast_le
    (F : DenseERSSequence B.C) {D : ℕ} (_hD : 0 < D) (k : ℕ) :
    (F.reciprocalSpecialThreshold D k : ℚ) /
        F.baseExpansionSize k ≤ 1 / D := by
  have hN : (0 : ℚ) < F.baseExpansionSize k := by
    exact_mod_cast F.baseExpansionSize_pos k
  have hfloor :
      (F.reciprocalSpecialThreshold D k : ℚ) ≤
        (F.baseExpansionSize k : ℚ) / D := by
    simpa [reciprocalSpecialThreshold] using
      (Nat.cast_div_le (m := F.baseExpansionSize k) (n := D) :
        ((F.baseExpansionSize k / D : ℕ) : ℚ) ≤
          (F.baseExpansionSize k : ℚ) / D)
  apply (div_le_iff hN).2
  calc
    (F.reciprocalSpecialThreshold D k : ℚ) ≤
        (F.baseExpansionSize k : ℚ) / D := hfloor
    _ = (1 / (D : ℚ)) * F.baseExpansionSize k := by ring

theorem div_lt_reciprocalSpecialThreshold_add_one
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ) :
    (F.baseExpansionSize k : ℚ) / D <
      F.reciprocalSpecialThreshold D k + 1 := by
  have hnat := Nat.lt_mul_div_succ (F.baseExpansionSize k) hD
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  apply (div_lt_iff hDq).2
  exact_mod_cast (by
    simpa [reciprocalSpecialThreshold, Nat.mul_comm] using hnat)

theorem reciprocalDeletionAllowance_cast_div_le
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ) :
    (F.reciprocalDeletionAllowance D k : ℚ) /
        F.baseExpansionSize k ≤
      2 / D + 2 / F.baseExpansionSize k := by
  have hN : (0 : ℚ) < F.baseExpansionSize k := by
    exact_mod_cast F.baseExpansionSize_pos k
  have hfloor :
      (F.baseExpansionSize k / D : ℕ) ≤
        (F.baseExpansionSize k : ℚ) / D := by
    exact Nat.cast_div_le
  unfold reciprocalDeletionAllowance
  push_cast
  apply (div_le_iff hN).2
  calc
    (2 : ℚ) * (F.baseExpansionSize k / D : ℕ) + 2 ≤
        2 * ((F.baseExpansionSize k : ℚ) / D) + 2 := by linarith
    _ = (2 / (D : ℚ) + 2 / F.baseExpansionSize k) *
        F.baseExpansionSize k := by field_simp; ring

theorem reciprocalDeletionAllowance_div_le_four
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (hlarge : D ≤ F.baseExpansionSize k) :
    (F.reciprocalDeletionAllowance D k : ℚ) /
      F.baseExpansionSize k ≤ 4 / D := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hlargeQ : (D : ℚ) ≤ F.baseExpansionSize k := by exact_mod_cast hlarge
  have hrecip : 2 / (F.baseExpansionSize k : ℚ) ≤ 2 / D := by
    exact div_le_div_of_nonneg_left (by norm_num) hDq hlargeQ
  calc
    (F.reciprocalDeletionAllowance D k : ℚ) /
        F.baseExpansionSize k ≤
      2 / D + 2 / F.baseExpansionSize k :=
        F.reciprocalDeletionAllowance_cast_div_le hD k
    _ ≤ 2 / D + 2 / D := add_le_add_left hrecip _
    _ = 4 / D := by ring

theorem reciprocalDeletionAllowance_le_baseExpansionSize
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 4 ≤ D) (k : ℕ)
    (hN : 4 ≤ F.baseExpansionSize k) :
    F.reciprocalDeletionAllowance D k ≤ F.baseExpansionSize k := by
  have hdiv := Nat.div_mul_le_self (F.baseExpansionSize k) D
  have hfour : 4 * (F.baseExpansionSize k / D) ≤ F.baseExpansionSize k := by
    calc
      4 * (F.baseExpansionSize k / D) ≤
          D * (F.baseExpansionSize k / D) :=
        Nat.mul_le_mul_right _ hD
      _ ≤ F.baseExpansionSize k := by
        simpa [Nat.mul_comm] using hdiv
  unfold reciprocalDeletionAllowance
  omega

theorem canonical_add_reciprocalDeletionAllowance_le_two
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 4 ≤ D) (k : ℕ)
    (hN : 4 ≤ F.baseExpansionSize k) :
    B.edgeCount * (F.r k) ^ B.P +
        F.reciprocalDeletionAllowance D k ≤
      2 * F.baseExpansionSize k := by
  exact Nat.add_le_add (F.canonicalSize_le_baseExpansionSize k)
    (F.reciprocalDeletionAllowance_le_baseExpansionSize hD k hN) |>.trans_eq
      (by omega)

end DenseERSSequence

end ERSFamily

end Formal.Streaming
