import SemiStreamingMatching.Proofs.Blueprint.MaxClass
import SemiStreamingMatching.Proofs.Blueprint.StartDistribution

open scoped BigOperators

namespace PaperConstructionEstimate

open GamblerWalk

noncomputable def finiteMaxMass (m K k j : ℕ) : ℝ :=
  (∑ s : Fin (StartDistribution.sampleCount m),
      ambientMaxZeroProbability (H := k * K) (StartDistribution.start m s) j) /
    StartDistribution.sampleCount m

theorem finiteMaxMass_nonneg (m K k j : ℕ) : 0 ≤ finiteMaxMass m K k j := by
  unfold finiteMaxMass
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro s _
    unfold ambientMaxZeroProbability
    apply div_nonneg
    · exact_mod_cast Nat.zero_le (ambientMaxZeroWords (2 * m) (k * K)
        (StartDistribution.start m s) j).card
    · positivity
  · exact_mod_cast Nat.zero_le (StartDistribution.sampleCount m)

theorem finiteMaxMass_approx_maxMass {m K k j : ℕ} (hNK : 2 * m ≤ K)
    (hj : 1 ≤ j) (hjtop : j < 2 * m) :
    |finiteMaxMass m K k j - StartDistribution.maxMass m j| ≤
      failureRatio K ^ k := by
  letI : Nonempty (Fin (StartDistribution.sampleCount m)) :=
    Fin.pos_iff_nonempty.mp (StartDistribution.sampleCount_pos m)
  have h := average_ambientMaxZeroProbability_approx
    (S := Fin (StartDistribution.sampleCount m)) (N := 2 * m) (K := K) (k := k) (j := j)
    hNK hj hjtop (StartDistribution.start m)
  simpa [finiteMaxMass, StartDistribution.maxMass] using h

theorem finiteMaxMass_pair_close {m K k j : ℕ} (hm : 0 < m) (hNK : 2 * m ≤ K)
    (hj : 1 ≤ j) (hjtop : j < 2 * m) :
    |finiteMaxMass m K k j - finiteMaxMass m K k (2 * m - j)| ≤
      2 * failureRatio K ^ k := by
  have hj' : 1 ≤ 2 * m - j := by omega
  have hj'top : 2 * m - j < 2 * m := by omega
  have hleft := finiteMaxMass_approx_maxMass (k := k) hNK hj hjtop
  have hright := finiteMaxMass_approx_maxMass (k := k) hNK hj' hj'top
  have hsymm := StartDistribution.maxMass_symm hm hj hjtop
  rw [← hsymm] at hright
  calc
    |finiteMaxMass m K k j - finiteMaxMass m K k (2 * m - j)| ≤
        |finiteMaxMass m K k j - StartDistribution.maxMass m j| +
          |StartDistribution.maxMass m j - finiteMaxMass m K k (2 * m - j)| :=
      abs_sub_le _ _ _
    _ = |finiteMaxMass m K k j - StartDistribution.maxMass m j| +
          |finiteMaxMass m K k (2 * m - j) - StartDistribution.maxMass m j| := by
      rw [abs_sub_comm (StartDistribution.maxMass m j)]
    _ ≤ failureRatio K ^ k + failureRatio K ^ k := add_le_add hleft hright
    _ = 2 * failureRatio K ^ k := by ring

theorem sum_maxKernel_Ico {i N : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    ∑ j in Finset.Ico 1 N,
        (if i ≤ j then (i : ℝ) / ((j : ℝ) * (j + 1)) else 0) =
      ((N - i : ℕ) : ℝ) / N := by
  induction N, hiN using Nat.le_induction with
  | base =>
      have hzero : ∑ j in Finset.Ico 1 i,
          (if i ≤ j then (i : ℝ) / ((j : ℝ) * (j + 1)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hjmem
        rw [if_neg]
        exact not_le_of_gt (Finset.mem_Ico.mp hjmem).2
      rw [hzero]
      simp
  | succ n hin ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n), if_pos hin, ih]
      have hnpos : 0 < n := by omega
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      have hn10 : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [Nat.cast_sub hin, Nat.cast_sub (by omega : i ≤ n + 1)]
      push_cast
      field_simp [hn0, hn10]
      ring

theorem sum_maxMass_Ico {m : ℕ} (hm : 0 < m) :
    ∑ j in Finset.Ico 1 (2 * m), StartDistribution.maxMass m j =
      (2 * (m : ℝ)) / (3 * m + 1) := by
  calc
    ∑ j in Finset.Ico 1 (2 * m), StartDistribution.maxMass m j =
        ∑ j in Finset.Ico 1 (2 * m),
          ((∑ s : Fin (StartDistribution.sampleCount m),
              if (StartDistribution.start m s).val ≤ j then
                ((StartDistribution.start m s).val : ℝ) / ((j : ℝ) * (j + 1))
              else 0) / StartDistribution.sampleCount m) := by
      rfl
    _ = (∑ j in Finset.Ico 1 (2 * m),
          ∑ s : Fin (StartDistribution.sampleCount m),
            if (StartDistribution.start m s).val ≤ j then
              ((StartDistribution.start m s).val : ℝ) / ((j : ℝ) * (j + 1))
            else 0) / StartDistribution.sampleCount m := by
      rw [Finset.sum_div]
    _ = (∑ s : Fin (StartDistribution.sampleCount m),
          ∑ j in Finset.Ico 1 (2 * m),
            if (StartDistribution.start m s).val ≤ j then
              ((StartDistribution.start m s).val : ℝ) / ((j : ℝ) * (j + 1))
            else 0) / StartDistribution.sampleCount m := by
      rw [Finset.sum_comm]
    _ = (∑ s : Fin (StartDistribution.sampleCount m),
          (((2 * m - (StartDistribution.start m s).val : ℕ) : ℝ) / (2 * m : ℕ))) /
          StartDistribution.sampleCount m := by
      congr 1
      apply Fintype.sum_congr
      intro s
      exact sum_maxKernel_Ico (StartDistribution.start_support hm s).1
        ((StartDistribution.start_support hm s).2.trans (by omega))
    _ = (2 * (m : ℝ)) / (3 * m + 1) := StartDistribution.mean_ruin hm

end PaperConstructionEstimate
