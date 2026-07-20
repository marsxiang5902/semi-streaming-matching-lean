import SemiStreamingMatching.Proofs.Framework.Amplification
import SemiStreamingMatching.Proofs.Framework.AppendixBSupports
import SemiStreamingMatching.Proofs.Framework.CommunicationHardnessBridge
import SemiStreamingMatching.Proofs.Framework.ConcreteParameters
import SemiStreamingMatching.Proofs.Framework.DeletionVariance
import SemiStreamingMatching.Proofs.Framework.HardFamilyAssembly

namespace Formal.Streaming

open scoped BigOperators

namespace ERSFamily

namespace DenseERSSequence

open HardDistribution SimpleExpansion AugmentedExpansion

variable {B : SimpleProperBlueprint}

theorem reciprocal_compression_numeric
    (D P N t bits : ℕ) (hD : 0 < D) (hP : 0 < P) (hN : 0 < N)
    (hbits : (2560 * D ^ 3 * P ^ 2) * bits ≤ 2 * N * t)
    (ht : 12800 * D ^ 3 * P ^ 2 ≤ t) :
    20 * (P : ℝ) ^ 2 / ((t : ℝ) * ((1 : ℝ) / (2 * D))) *
          ((bits : ℝ) * Real.log 2 + 5 * Real.log (2 * N)) ≤
      ((1 : ℝ) / (16 * D)) * ((N / D : ℕ) + 1) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have htreal : (0 : ℝ) < t := by
    have : 0 < 12800 * D ^ 3 * P ^ 2 := by positivity
    exact_mod_cast (this.trans_le ht)
  have hscaleReal : (0 : ℝ) < 2560 * D ^ 3 * P ^ 2 := by positivity
  have hbitsReal :
      (2560 : ℝ) * D ^ 3 * P ^ 2 * bits ≤ 2 * N * t := by
    exact_mod_cast hbits
  have htReal :
      (12800 : ℝ) * D ^ 3 * P ^ 2 ≤ t := by
    exact_mod_cast ht
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogN : 5 * Real.log (2 * (N : ℝ)) ≤ 10 * N := by
    have hpos : (0 : ℝ) < 2 * N := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    nlinarith
  have hbitsTerm :
      (40 : ℝ) * D * P ^ 2 / t * ((bits : ℝ) * Real.log 2) ≤
        (N : ℝ) / ((32 : ℝ) * D ^ 2) := by
    have hlogMul : (bits : ℝ) * Real.log 2 ≤ bits := by
      simpa using mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg bits)
    have hbitsBound :
        (bits : ℝ) ≤
          ((2 : ℝ) * N * t) / ((2560 : ℝ) * D ^ 3 * P ^ 2) := by
      apply (le_div_iff hscaleReal).2
      nlinarith [hbitsReal]
    calc
      (40 : ℝ) * D * P ^ 2 / t * ((bits : ℝ) * Real.log 2) ≤
          (40 : ℝ) * D * P ^ 2 / t * bits := by
            exact mul_le_mul_of_nonneg_left hlogMul (by positivity)
      _ ≤ (40 : ℝ) * D * P ^ 2 / t *
          (((2 : ℝ) * N * t) / ((2560 : ℝ) * D ^ 3 * P ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hbitsBound (by positivity)
      _ = (N : ℝ) / ((32 : ℝ) * D ^ 2) := by field_simp; ring
  have hlogTerm :
      (40 : ℝ) * D * P ^ 2 / t * (5 * Real.log (2 * (N : ℝ))) ≤
        (N : ℝ) / ((32 : ℝ) * D ^ 2) := by
    have htBound :
        ((40 : ℝ) * D * P ^ 2 / t) ≤
          1 / ((320 : ℝ) * D ^ 2) := by
      apply (div_le_iff htreal).2
      rw [show (1 / ((320 : ℝ) * D ^ 2)) * t =
        t / ((320 : ℝ) * D ^ 2) by ring]
      apply (le_div_iff (by positivity : (0 : ℝ) < (320 : ℝ) * D ^ 2)).2
      nlinarith [htReal]
    calc
      (40 : ℝ) * D * P ^ 2 / t * (5 * Real.log (2 * (N : ℝ))) ≤
          (40 : ℝ) * D * P ^ 2 / t * ((10 : ℝ) * N) := by
            exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      _ ≤ (1 / ((320 : ℝ) * D ^ 2)) * ((10 : ℝ) * N) := by
            exact mul_le_mul_of_nonneg_right htBound (by positivity)
      _ = (N : ℝ) / ((32 : ℝ) * D ^ 2) := by ring
  have hthreshold :
      (N : ℝ) / D < ((N / D : ℕ) : ℝ) + 1 := by
    have hnat := Nat.lt_mul_div_succ N hD
    apply (div_lt_iff hDreal).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hnat)
  have hrhs :
      (N : ℝ) / ((16 : ℝ) * D ^ 2) ≤
        ((1 : ℝ) / (16 * D)) * (((N / D : ℕ) : ℝ) + 1) := by
    have hfactor : (0 : ℝ) ≤ 1 / (16 * D) := by positivity
    have := mul_le_mul_of_nonneg_left hthreshold.le hfactor
    calc
      (N : ℝ) / ((16 : ℝ) * D ^ 2) =
          ((1 : ℝ) / (16 * D)) * ((N : ℝ) / D) := by
            ring_nf
      _ ≤ ((1 : ℝ) / (16 * D)) * (((N / D : ℕ) : ℝ) + 1) := this
  have hcoefficient :
      20 * (P : ℝ) ^ 2 / ((t : ℝ) * ((1 : ℝ) / (2 * D))) =
        40 * D * P ^ 2 / t := by field_simp; ring
  rw [hcoefficient]
  calc
    (40 : ℝ) * D * P ^ 2 / t *
          ((bits : ℝ) * Real.log 2 + 5 * Real.log (2 * N)) =
        (40 : ℝ) * D * P ^ 2 / t * ((bits : ℝ) * Real.log 2) +
          (40 : ℝ) * D * P ^ 2 / t * (5 * Real.log (2 * N)) := by ring
    _ ≤ (N : ℝ) / ((32 : ℝ) * D ^ 2) +
        (N : ℝ) / ((32 : ℝ) * D ^ 2) :=
      add_le_add hbitsTerm hlogTerm
    _ = (N : ℝ) / ((16 : ℝ) * D ^ 2) := by ring
    _ ≤ ((1 : ℝ) / (16 * D)) * ((N / D : ℕ) + 1) := hrhs

theorem blueprintPart_nonempty_of_part_nonempty
    (F : DenseERSSequence B.C) (k : ℕ)
    (J : IndexTuple B (F.t k)) (p : Fin B.P)
    (hpart : (part B (F.host k) J p).Nonempty) :
    (B.E p).Nonempty := by
  have hcard : 0 < (part B (F.host k) J p).card :=
    Finset.card_pos.mpr hpart
  rw [part_card] at hcard
  have hEcard : 0 < (B.E p).card := by
    by_contra hzero
    have : (B.E p).card = 0 := Nat.eq_zero_of_not_pos hzero
    simp [this] at hcard
  exact Finset.card_pos.mp hEcard

theorem reciprocalDeletionBadBound
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 0 < D) (k : ℕ)
    (hlarge : 16 * D ^ 2 ≤ F.baseExpansionSize k) :
    CanonicalDeletionBadBound B (F.host k) (F.reciprocalDeletions D k)
      (F.reciprocalDeletionAllowance D k) ((1 : ℚ) / (16 * D)) := by
  let N := F.baseExpansionSize k
  let M := B.edgeCount * (F.r k) ^ B.P
  have hNpos : 0 < N := by simpa [N] using F.baseExpansionSize_pos k
  have hNq : (0 : ℚ) < N := by exact_mod_cast hNpos
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hMle : M ≤ N := by simpa [M, N] using F.canonicalSize_le_baseExpansionSize k
  have hMleQ : (M : ℚ) ≤ N := by exact_mod_cast hMle
  have hlargeQ : (16 : ℚ) * D ^ 2 ≤ N := by exact_mod_cast hlarge
  refine canonicalDeletionBadBound_of_variance B (F.host k)
    (F.reciprocalDeletions D k)
    (F.reciprocalDeletions_admissible (by omega) k)
    (delta := (1 : ℚ) / D) (a := (N : ℚ) / D) ?_ ?_ ?_ ?_
  · intro J p
    exact floorDeletionCount_cast_le_rate_mul_part_card
      B (F.host k) 1 D J p hD
  · positivity
  · have hprob : (((1 : ℚ) / D) * (M : ℚ)) / ((N : ℚ) / D) ^ 2 ≤
      (1 : ℚ) / (16 * D) := by
      have hmain : (16 : ℚ) * (M : ℚ) * (D : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
        calc
          (16 : ℚ) * (M : ℚ) * (D : ℚ) ^ 2 ≤
              16 * (N : ℚ) * (D : ℚ) ^ 2 := by gcongr
          _ = ((16 : ℚ) * D ^ 2) * N := by ring
          _ ≤ (N : ℚ) * N :=
            mul_le_mul_of_nonneg_right hlargeQ (by positivity)
          _ = (N : ℚ) ^ 2 := by ring
      rw [show (((1 : ℚ) / D) * (M : ℚ)) / ((N : ℚ) / D) ^ 2 =
          ((M : ℚ) * D) / (N : ℚ) ^ 2 by
        field_simp [ne_of_gt hDq, ne_of_gt hNq]
        <;> ring]
      apply (div_le_div_iff (sq_pos_of_pos hNq)
        (by positivity : (0 : ℚ) < 16 * D)).2
      nlinarith [hmain]
    simpa [M, Nat.cast_mul, Nat.cast_pow] using hprob
  · have hthreshold : ((1 : ℚ) / D) * (M : ℚ) + (N : ℚ) / D ≤
        F.reciprocalDeletionAllowance D k := by
      have hquot := F.div_lt_reciprocalSpecialThreshold_add_one hD k
      have hmean : ((1 : ℚ) / D) * (M : ℚ) ≤ (N : ℚ) / D := by
        have hnonneg : (0 : ℚ) ≤ 1 / D := by positivity
        have := mul_le_mul_of_nonneg_left hMleQ hnonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      simp only [reciprocalSpecialThreshold, N] at hquot
      unfold reciprocalDeletionAllowance
      push_cast
      linarith
    simpa [M, Nat.cast_mul, Nat.cast_pow] using hthreshold

theorem loss_eq_reciprocal
    (F : DenseERSSequence B.C) (D : ℕ)
    (hnum : F.relativeLossNumerator = 1)
    (hden : F.relativeLossDenominator = 64 * D * B.P) :
    F.loss = (1 : ℚ) / (64 * D * B.P) := by
  unfold loss
  rw [hnum, hden]
  push_cast
  rfl

theorem reciprocal_gap_on_good
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (k : ℕ) (hbase : D ≤ F.baseExpansionSize k)
    (hfour : 4 ≤ F.baseExpansionSize k)
    (sample : Sample B (F.host k) (F.reciprocalDeletions D k))
    (hgood : CanonicalDeletionGood (F.reciprocalDeletionAllowance D k) sample) :
    (((exactSampleCertificate sample).ordinaryUpper +
        F.reciprocalSpecialThreshold D k : ℕ) : ℚ) <
      (blueprintRatioRat B + (49 : ℚ) / D) *
        (exactSampleCertificate sample).optimumLower := by
  have hDpos : 0 < D := by omega
  have hDq : (0 : ℚ) < D := by exact_mod_cast hDpos
  have hPq : (0 : ℚ) < B.P := by exact_mod_cast B.hP
  have ha : B.P * F.loss = (1 : ℚ) / (64 * D) := by
    rw [hloss]
    field_simp [ne_of_gt hDq, ne_of_gt hPq]
    <;> ring
  have hdensity := F.canonical_density_bounds B k sample.1
  rw [canonicalMatching_card, expansion_left_card] at hdensity
  apply exactSampleCertificate_gap_of_good B (F.host k) sample hgood
    (qSpecial := F.reciprocalSpecialThreshold D k)
    (a := B.P * F.loss) (eta := (6 : ℚ) / D)
    (epsilon := (49 : ℚ) / D)
  · simpa [baseExpansionSize] using
      F.canonical_add_reciprocalDeletionAllowance_le_two (by omega) k hfour
  · exact mul_nonneg (by positivity) F.loss_nonneg
  · positivity
  · apply (div_le_iff hDq).2
    have hDcast : (12 : ℚ) ≤ D := by exact_mod_cast hD
    nlinarith
  · exact hdensity.1
  · exact hdensity.2
  · have hthreshold := F.reciprocalSpecialThreshold_cast_le hDpos k
    rw [ha]
    have hnumeric :
      2 * ((1 : ℚ) / (64 * D)) +
          (F.reciprocalSpecialThreshold D k : ℚ) /
            F.baseExpansionSize k ≤ (6 : ℚ) / D := by
      calc
        2 * ((1 : ℚ) / (64 * D)) +
            (F.reciprocalSpecialThreshold D k : ℚ) /
              F.baseExpansionSize k ≤
          2 * ((1 : ℚ) / (64 * D)) + 1 / D := by linarith
        _ ≤ (6 : ℚ) / D := by
          rw [show 2 * ((1 : ℚ) / (64 * D)) + 1 / D =
            ((33 : ℚ) / 32) / D by ring]
          exact (div_le_div_right hDq).2 (by norm_num)
    simpa [baseExpansionSize] using hnumeric
  · have hallowance := F.reciprocalDeletionAllowance_div_le_four hDpos k hbase
    rw [ha]
    have hnumeric :
      (1 : ℚ) / (64 * D) +
          (F.reciprocalDeletionAllowance D k : ℚ) /
            F.baseExpansionSize k ≤ (6 : ℚ) / D := by
      calc
        (1 : ℚ) / (64 * D) +
            (F.reciprocalDeletionAllowance D k : ℚ) /
              F.baseExpansionSize k ≤
          (1 : ℚ) / (64 * D) + 4 / D := by linarith
        _ ≤ (6 : ℚ) / D := by
          rw [show (1 : ℚ) / (64 * D) + 4 / D =
            ((257 : ℚ) / 64) / D by ring]
          exact (div_le_div_right hDq).2 (by norm_num)
    simpa [baseExpansionSize] using hnumeric
  · rw [show 8 * ((6 : ℚ) / D) = 48 / D by ring]
    exact (div_lt_div_right hDq).2 (by norm_num)

noncomputable def reciprocalStructuredDistribution
    (F : DenseERSSequence B.C) (D k : ℕ) (hD : 1 ≤ D) :=
  finitePartitionDistribution B (F.host k) (F.reciprocalDeletions D k)
    (F.reciprocalDeletions_admissible hD k)

noncomputable def reciprocalDistribution
    (F : DenseERSSequence B.C) (D k : ℕ) (hD : 1 ≤ D) :
    FinitePartitionDistribution (B.P + 1)
      (Fin (F.augmentedExpansionSize B.P k))
      (Fin (F.augmentedExpansionSize B.P k)) :=
  (F.reciprocalStructuredDistribution D k hD).relabel
    (F.augmentedLeftEquivFin k) (F.augmentedRightEquivFin k)

theorem reciprocal_communicationHard
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (k bits : ℕ)
    (hbase : 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hsum : ExactRecoverableSpecialSumBound
      (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
      B (F.host k) (F.reciprocalDeletions D k)
      (F.reciprocalDeletions_admissible (by omega) k)
      bits (F.reciprocalSpecialThreshold D k)
      ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D))) :
    (F.reciprocalDistribution D k (by omega)).IsHardForCommunication
      (blueprintRatioRat B + (49 : ℚ) / D)
      (1 - (1 : ℚ) / (8 * D)) bits := by
  have hDpos : 0 < D := by omega
  have hDq : (0 : ℚ) < D := by exact_mod_cast hDpos
  have hfour : 4 ≤ F.baseExpansionSize k := by
    have : 4 ≤ 16 * D ^ 2 := by nlinarith
    exact this.trans hbase
  have hbaseD : D ≤ F.baseExpansionSize k := by
    have : D ≤ 16 * D ^ 2 := by nlinarith
    exact this.trans hbase
  have hstructured :
      (F.reciprocalStructuredDistribution D k (by omega)).IsHardForCommunication
        (blueprintRatioRat B + (49 : ℚ) / D)
        ((1 : ℚ) / (16 * D) +
          (1 - (1 : ℚ) / (4 * D) + (1 : ℚ) / (16 * D))) bits := by
    apply communicationHardness_of_good_exactRecoverableSpecialSum_assembly
      B (F.host k) (F.reciprocalDeletions D k)
      (F.reciprocalDeletions_admissible (by omega) k)
      (deletionAllowance := F.reciprocalDeletionAllowance D k)
      (specialThreshold := F.reciprocalSpecialThreshold D k)
      (rho := blueprintRatioRat B + (49 : ℚ) / D)
      (eta := (1 : ℚ) / (4 * D))
      (beta := (1 : ℚ) / (16 * D))
      (pBad := (1 : ℚ) / (16 * D))
    · apply (div_le_one (by positivity : (0 : ℚ) < 4 * D)).2
      exact_mod_cast (show 1 ≤ 4 * D by omega)
    · have hratio : (0 : ℚ) ≤ blueprintRatioRat B := by
        have hreal : (0 : ℝ) ≤ (blueprintRatioRat B : ℝ) := by
          simpa only [blueprintRatioRat_cast] using blueprintRatio_nonneg B
        exact_mod_cast hreal
      positivity
    · intro sample hgood
      exact F.reciprocal_gap_on_good hD hloss k hbaseD hfour sample hgood
    · exact (F.reciprocalDeletionBadBound hDpos k hbase).card_le
    · exact hsum
  have hstructured' :
      (F.reciprocalStructuredDistribution D k (by omega)).IsHardForCommunication
        (blueprintRatioRat B + (49 : ℚ) / D)
        (1 - (1 : ℚ) / (8 * D)) bits := by
    convert hstructured using 1 <;> field_simp [ne_of_gt hDq] <;> ring
  exact hstructured'.relabel
    (F.augmentedLeftEquivFin k) (F.augmentedRightEquivFin k)

noncomputable def reciprocalSequentialHardFamily
    (F : DenseERSSequence B.C) (D : ℕ) (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (hbase : ∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hrecover : ∀ k bits,
      reciprocalCommunicationScale B D * bits ≤
          F.augmentedExpansionSize B.P k * F.t k →
        ExactRecoverableSpecialSumBound
          (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
          B (F.host k) (F.reciprocalDeletions D k)
          (F.reciprocalDeletions_admissible (by omega) k)
          bits (F.reciprocalSpecialThreshold D k)
          ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D))) :
    SequentialBlueprintHardFamily B where
  size := F.augmentedExpansionSize B.P
  hostMultiplicity := F.t
  distribution := fun k ↦ F.reciprocalDistribution D k (by omega)
  approximation := blueprintRatioRat B + (49 : ℚ) / D
  successThreshold := 1 - (1 : ℚ) / (8 * D)
  communicationScale := reciprocalCommunicationScale B D
  spaceDomination := by
    intro space hspace
    exact F.semiStreaming_space_domination B hspace
      (reciprocalCommunicationScale B D)
  communicationHard := by
    intro k bits hbits
    exact F.reciprocal_communicationHard hD hloss k bits (hbase k)
      (hrecover k bits hbits)

@[simp]
theorem reciprocalSequentialHardFamily_hasAmplifiableParameters
    (F : DenseERSSequence B.C) (D : ℕ) (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (hbase : ∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hrecover : ∀ k bits,
      reciprocalCommunicationScale B D * bits ≤
          F.augmentedExpansionSize B.P k * F.t k →
        ExactRecoverableSpecialSumBound
          (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
          B (F.host k) (F.reciprocalDeletions D k)
          (F.reciprocalDeletions_admissible (by omega) k)
          bits (F.reciprocalSpecialThreshold D k)
          ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D))) :
    (F.reciprocalSequentialHardFamily D hD hloss hbase hrecover).HasAmplifiableParameters
      ((49 : ℚ) / D) ((1 : ℚ) / (8 * D)) := by
  exact ⟨rfl, le_rfl⟩

theorem exists_reciprocal_tail
    (B : SimpleProperBlueprint) (D : ℕ) (hD : 12 ≤ D) :
    ∃ F : DenseERSSequence B.C,
      F.loss = (1 : ℚ) / (64 * D * B.P) ∧
      (∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k) ∧
      (∀ k, 12800 * D ^ 3 * B.P ^ 2 ≤ F.t k) ∧
      (∀ k p, (B.E p).Nonempty →
        D ≤ playerPartSize B (F.r k) (F.t k) p) := by
  have hDpos : 0 < D := by omega
  have hlt : 1 < 64 * D * B.P := by
    calc
      1 < 64 := by norm_num
      _ = 64 * 1 * 1 := by norm_num
      _ ≤ 64 * D * B.P := by
        gcongr
        · omega
        · exact B.hP
  obtain ⟨F₀, hnum, hden⟩ :=
    AppendixBSupports.exists_denseERSSequence B.C 1 (64 * D * B.P)
      B.hC (by omega) hlt
  obtain ⟨offset, htail⟩ := F₀.exists_uniform_tail_bounds
    (16 * D ^ 2) D (12800 * D ^ 3 * B.P ^ 2)
  let F := F₀.tail offset
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · apply F.loss_eq_reciprocal D
    · exact hnum
    · exact hden
  · intro k
    simpa [F, baseExpansionSize] using (htail k).1
  · intro k
    simpa [F] using (htail k).2.1
  · intro k p hp
    simpa [F] using (htail k).2.2 p hp

theorem reciprocal_exactRecoverableSpecialSumBound
    (F : DenseERSSequence B.C) {D : ℕ} (hD : 12 ≤ D) (k bits : ℕ)
    (hactive : ∀ p : Fin B.P, (B.E p).Nonempty →
      D ≤ playerPartSize B (F.r k) (F.t k) p)
    (ht : 12800 * D ^ 3 * B.P ^ 2 ≤ F.t k)
    (hbits : reciprocalCommunicationScale B D * bits ≤
      F.augmentedExpansionSize B.P k * F.t k) :
    ExactRecoverableSpecialSumBound
      (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
      B (F.host k) (F.reciprocalDeletions D k)
      (F.reciprocalDeletions_admissible (by omega) k)
      bits (F.reciprocalSpecialThreshold D k)
      ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D)) := by
  have hDpos : 0 < D := by omega
  have hNpos := F.baseExpansionSize_pos k
  have hbits' :
      (2560 * D ^ 3 * B.P ^ 2) * bits ≤
        2 * F.baseExpansionSize k * F.t k := by
    simpa [reciprocalCommunicationScale, ERSSequence.augmentedExpansionSize,
      baseExpansionSize] using hbits
  apply exactRecoverableSpecialSumBound_of_compression
    B (F.host k) (F.reciprocalDeletions D k)
      (F.reciprocalDeletions_admissible (by omega) k)
      bits (F.reciprocalSpecialThreshold D k)
      ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D))
      ((1 : ℝ) / (2 * D))
      (5 * Real.log (2 * F.baseExpansionSize k))
  · positivity
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have hN : 1 ≤ F.baseExpansionSize k := hNpos
      exact_mod_cast (show 1 ≤ 2 * F.baseExpansionSize k by omega)))
  · intro J p hpart
    exact F.reciprocalDeletions_pos_of_part_nonempty
      hDpos k hactive J p hpart
  · intro J p _hpart
    exact F.two_mul_reciprocalDeletions_le_part (by omega) k J p
  · intro J p hpart
    exact F.reciprocalDeletions_real_rate_lower hDpos k J p
      (F.reciprocalDeletions_pos_of_part_nonempty hDpos k hactive J p hpart)
  · intro J p _hpart
    exact F.reciprocal_player_log_bound k J p
  · norm_num
    push_cast
    ring_nf
    exact le_rfl
  · simpa [reciprocalSpecialThreshold, baseExpansionSize] using
      (reciprocal_compression_numeric D B.P (F.baseExpansionSize k) (F.t k)
        bits hDpos B.hP hNpos hbits' ht)

theorem reciprocal_tail_defeats
    (F : DenseERSSequence B.C) (D : ℕ) (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (hbase : ∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hrecover : ∀ k bits,
      reciprocalCommunicationScale B D * bits ≤
          F.augmentedExpansionSize B.P k * F.t k →
        ExactRecoverableSpecialSumBound
          (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
          B (F.host k) (F.reciprocalDeletions D k)
          (F.reciprocalDeletions_admissible (by omega) k)
          bits (F.reciprocalSpecialThreshold D k)
          ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D)))
    {epsilon : ℚ} (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (happrox : (49 : ℚ) / D < epsilon)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.reciprocalDistribution D k (by omega)).Sample,
        (A.algorithm (F.augmentedExpansionSize B.P k)).successProbability
            (blueprintRatioRat B + epsilon)
            ((F.reciprocalDistribution D k (by omega)).input x).graph
            ((F.reciprocalDistribution D k (by omega)).input x).stream ≤
          1 - epsilon := by
  let G₀ := F.reciprocalSequentialHardFamily D hD hloss hbase hrecover
  have hraise : G₀.approximation ≤ blueprintRatioRat B + epsilon := by
    dsimp [G₀, reciprocalSequentialHardFamily]
    linarith
  let G := G₀.raiseApproximation (blueprintRatioRat B + epsilon) hraise
  have hparameters : G.HasAmplifiableParameters epsilon ((1 : ℚ) / (8 * D)) := by
    exact ⟨rfl, le_rfl⟩
  have hgamma : (0 : ℚ) < (1 : ℚ) / (8 * D) := by positivity
  have hresult := G.blueprint_to_semiStreaming_lower_bound_amplified_of_unit
    hparameters hepsilon0.le hepsilon1 hgamma A
  simpa [G, G₀, SequentialBlueprintHardFamily.raiseApproximation,
    reciprocalSequentialHardFamily] using hresult

theorem reciprocal_tail_defeats_general
    (F : DenseERSSequence B.C) (D : ℕ) (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (hbase : ∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hrecover : ∀ k bits,
      reciprocalCommunicationScale B D * bits ≤
          F.augmentedExpansionSize B.P k * F.t k →
        ExactRecoverableSpecialSumBound
          (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
          B (F.host k) (F.reciprocalDeletions D k)
          (F.reciprocalDeletions_admissible (by omega) k)
          bits (F.reciprocalSpecialThreshold D k)
          ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D)))
    {epsilon target : ℚ} (happrox : (49 : ℚ) / D < epsilon)
    (htarget0 : 0 < target) (htarget1 : target < 1)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.reciprocalDistribution D k (by omega)).Sample,
        (A.algorithm (F.augmentedExpansionSize B.P k)).successProbability
            (blueprintRatioRat B + epsilon)
            ((F.reciprocalDistribution D k (by omega)).input x).graph
            ((F.reciprocalDistribution D k (by omega)).input x).stream ≤
          target := by
  let G₀ := F.reciprocalSequentialHardFamily D hD hloss hbase hrecover
  have hraise : G₀.approximation ≤ blueprintRatioRat B + epsilon := by
    dsimp [G₀, reciprocalSequentialHardFamily]
    linarith
  let G := G₀.raiseApproximation (blueprintRatioRat B + epsilon) hraise
  have hparameters : G.HasAmplifiableParameters epsilon ((1 : ℚ) / (8 * D)) := by
    exact ⟨rfl, le_rfl⟩
  have hgamma : (0 : ℚ) < (1 : ℚ) / (8 * D) := by positivity
  have hresult := G.blueprint_to_semiStreaming_lower_bound_amplified_general
    hparameters htarget0 htarget1 hgamma A
  simpa [G, G₀, SequentialBlueprintHardFamily.raiseApproximation,
    reciprocalSequentialHardFamily] using hresult

theorem reciprocal_tail_defeats_infeasible
    (F : DenseERSSequence B.C) (D : ℕ) (hD : 12 ≤ D)
    (hloss : F.loss = (1 : ℚ) / (64 * D * B.P))
    (hbase : ∀ k, 16 * D ^ 2 ≤ F.baseExpansionSize k)
    (hrecover : ∀ k bits,
      reciprocalCommunicationScale B D * bits ≤
          F.augmentedExpansionSize B.P k * F.t k →
        ExactRecoverableSpecialSumBound
          (L0 := Fin (F.n k)) (R0 := Fin (F.n k))
          B (F.host k) (F.reciprocalDeletions D k)
          (F.reciprocalDeletions_admissible (by omega) k)
          bits (F.reciprocalSpecialThreshold D k)
          ((1 : ℚ) / (4 * D)) ((1 : ℚ) / (16 * D)))
    {epsilon : ℚ} (happrox : (49 : ℚ) / D < epsilon)
    (A : SemiStreamingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.reciprocalDistribution D k (by omega)).Sample,
        (A.algorithm (F.augmentedExpansionSize B.P k)).successProbability
            (blueprintRatioRat B + epsilon)
            ((F.reciprocalDistribution D k (by omega)).input x).graph
            ((F.reciprocalDistribution D k (by omega)).input x).stream ≤
          1 - (1 : ℚ) / (8 * D) := by
  let G₀ := F.reciprocalSequentialHardFamily D hD hloss hbase hrecover
  have hraise : G₀.approximation ≤ blueprintRatioRat B + epsilon := by
    dsimp [G₀, reciprocalSequentialHardFamily]
    linarith
  let G := G₀.raiseApproximation (blueprintRatioRat B + epsilon) hraise
  have hresult := G.defeats_semiStreaming A
  simpa [G, G₀, SequentialBlueprintHardFamily.raiseApproximation,
    reciprocalSequentialHardFamily] using hresult

theorem simpleProperBlueprint_semiStreaming_lower_bound
    (B : SimpleProperBlueprint) {epsilon : ℚ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ D : ℕ, ∃ F : DenseERSSequence B.C,
      ∃ hD : 12 ≤ D,
      F.loss = (1 : ℚ) / (64 * D * B.P) ∧
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
        ∃ x : (F.reciprocalDistribution D k (by omega)).Sample,
          (A.algorithm (F.augmentedExpansionSize B.P k)).successProbability
              (blueprintRatioRat B + epsilon)
              ((F.reciprocalDistribution D k (by omega)).input x).graph
              ((F.reciprocalDistribution D k (by omega)).input x).stream ≤
            1 - epsilon := by
  obtain ⟨D, hD, happrox⟩ := exists_reciprocal_denominator hepsilon0
  obtain ⟨F, hloss, hbase, ht, hactive⟩ := exists_reciprocal_tail B D hD
  refine ⟨D, F, hD, hloss, ?_⟩
  refine F.reciprocal_tail_defeats D hD hloss hbase
    ?_ hepsilon0 hepsilon1 happrox A
  intro k bits hbits
  exact F.reciprocal_exactRecoverableSpecialSumBound hD k bits
    (hactive k) (ht k) hbits

end DenseERSSequence

end ERSFamily

end Formal.Streaming
