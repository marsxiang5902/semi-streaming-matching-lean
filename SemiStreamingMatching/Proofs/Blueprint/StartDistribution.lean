import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rat.Field
import Mathlib.Data.Rat.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace StartDistribution

def gammaQ (m : ℕ) : ℚ :=
  (2 * (m : ℚ) * (m + 1)) / (3 * m + 1)

def weightQ (m i : ℕ) : ℚ :=
  gammaQ m * (2 * (2 * (m : ℚ) + 1)) /
    ((2 * (m : ℚ) - (i + 1)) *
      (2 * (m : ℚ) - (i + 1) + 1) *
      (2 * (m : ℚ) - (i + 1) + 2))

lemma gammaQ_pos {m : ℕ} (hm : 0 < m) : 0 < gammaQ m := by
  unfold gammaQ
  positivity

lemma weightQ_nonneg {m i : ℕ} (hm : 0 < m) (hi : i < m) : 0 ≤ weightQ m i := by
  have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.2 hi)
  have hr : 0 < 2 * (m : ℚ) - (i + 1) := by
    have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
    linarith
  unfold weightQ
  have hg : 0 < gammaQ m := gammaQ_pos hm
  have hn : 0 < (2 * (2 * (m : ℚ) + 1)) := by positivity
  have hr1 : 0 < 2 * (m : ℚ) - (i + 1) + 1 := by linarith
  have hr2 : 0 < 2 * (m : ℚ) - (i + 1) + 2 := by linarith
  exact (div_pos (mul_pos hg hn) (mul_pos (mul_pos hr hr1) hr2)).le

private lemma r_ne_zero {m i : ℕ} (hm : 0 < m) (hi : i < m) :
    (2 * (m : ℚ) - (i + 1)) ≠ 0 := by
  have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.2 hi)
  have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
  linarith

lemma weightQ_eq_telescoping {m i : ℕ} (hm : 0 < m) (hi : i < m) :
    weightQ m i = gammaQ m * (2 * (m : ℚ) + 1) *
      (1 / ((2 * (m : ℚ) - (i + 1)) *
              (2 * (m : ℚ) - (i + 1) + 1)) -
       1 / ((2 * (m : ℚ) - (i + 1) + 1) *
              (2 * (m : ℚ) - (i + 1) + 2))) := by
  have h0 := r_ne_zero hm hi
  have h1 : 2 * (m : ℚ) - (i + 1) + 1 ≠ 0 := by
    have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.2 hi)
    have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
    linarith
  have h2 : 2 * (m : ℚ) - (i + 1) + 2 ≠ 0 := by
    have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.2 hi)
    have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
    linarith
  unfold weightQ
  field_simp
  ring

lemma sum_weightQ_range {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    ∑ i in Finset.range j, weightQ m i =
      gammaQ m * (2 * (m : ℚ) + 1) *
        (1 / ((2 * (m : ℚ) - j) * (2 * (m : ℚ) - j + 1)) -
         1 / ((2 * (m : ℚ)) * (2 * (m : ℚ) + 1))) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < m := Nat.lt_of_succ_le hj
      rw [Finset.sum_range_succ, ih (Nat.le_of_lt hjlt), weightQ_eq_telescoping hm hjlt]
      have hc : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by norm_num
      rw [hc]
      ring

lemma sum_weightQ_eq_one {m : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m, weightQ m i = 1 := by
  rw [sum_weightQ_range hm le_rfl]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2m : 2 * (m : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hm0
  have h2m1 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  have h3m1 : 3 * (m : ℚ) + 1 ≠ 0 := by positivity
  have htel :
      (1 / ((m : ℚ) * (m + 1)) -
        1 / ((2 * (m : ℚ)) * (2 * (m : ℚ) + 1))) =
        (3 * (m : ℚ) + 1) /
          (2 * (m : ℚ) * (m + 1) * (2 * (m : ℚ) + 1)) := by
    field_simp [hm0, hm1, h2m, h2m1]
    ring
  have hsub : 2 * (m : ℚ) - (m : ℚ) = m := by ring
  rw [hsub]
  rw [htel]
  unfold gammaQ
  field_simp [hm0, hm1, h2m, h2m1, h3m1, mul_ne_zero hm0 hm1]

lemma partial_momentQ {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    ∑ i in Finset.range j, weightQ m i * ((i + 1 : ℕ) : ℚ) =
      gammaQ m * (((j : ℚ) * (j + 1)) /
        ((2 * (m : ℚ) - j) * (2 * (m : ℚ) - j + 1))) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < m := Nat.lt_of_succ_le hj
      rw [Finset.sum_range_succ, ih (Nat.le_of_lt hjlt)]
      unfold weightQ
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      have hjQ : (j : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.2 hjlt)
      have h0 : 2 * (m : ℚ) - ((j : ℚ) + 1) ≠ 0 := by
        have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
        linarith
      have h1 : 2 * (m : ℚ) - ((j : ℚ) + 1) + 1 ≠ 0 := by linarith
      have h2 : 2 * (m : ℚ) - ((j : ℚ) + 1) + 2 ≠ 0 := by linarith
      have hp0 : 2 * (m : ℚ) - (j : ℚ) ≠ 0 := by
        have hmQ : 0 < (m : ℚ) := by exact_mod_cast hm
        linarith
      have hp1 : 2 * (m : ℚ) - (j : ℚ) + 1 ≠ 0 := by linarith
      push_cast
      field_simp [h0, h1, h2, hp0, hp1]
      ring

lemma total_momentQ {m : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m, weightQ m i * ((i + 1 : ℕ) : ℚ) = gammaQ m := by
  rw [partial_momentQ hm le_rfl]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hsub : 2 * (m : ℚ) - (m : ℚ) = m := by ring
  rw [hsub]
  rw [div_self (mul_ne_zero hm0 hm1), mul_one]

private def commonDenominator (m : ℕ) : ℕ :=
  ∏ i in Finset.range m, (weightQ m i).den

private def multiplicity (m i : ℕ) : ℕ :=
  commonDenominator m / (weightQ m i).den * (weightQ m i).num.natAbs

private lemma commonDenominator_pos (m : ℕ) : 0 < commonDenominator m := by
  unfold commonDenominator
  exact Finset.prod_pos fun i _ => (weightQ m i).den_pos

private lemma den_dvd_commonDenominator {m i : ℕ} (hi : i < m) :
    (weightQ m i).den ∣ commonDenominator m := by
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi)

private lemma multiplicity_ratio {m i : ℕ} (hm : 0 < m) (hi : i < m) :
    (multiplicity m i : ℚ) / commonDenominator m = weightQ m i := by
  have hdvd := den_dvd_commonDenominator hi
  have hD0 : (commonDenominator m : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos m).ne'
  have hden0 : ((weightQ m i).den : ℚ) ≠ 0 := by
    exact_mod_cast (weightQ m i).den_nz
  have hnum : ((weightQ m i).num.natAbs : ℤ) = (weightQ m i).num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.2 (weightQ_nonneg hm hi))
  have hnumQ : ((weightQ m i).num.natAbs : ℚ) = (weightQ m i).num := by
    rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.2 (weightQ_nonneg hm hi))]
  rw [multiplicity, Nat.cast_mul, Nat.cast_div hdvd hden0, hnumQ]
  calc
    (↑(commonDenominator m) / ↑(weightQ m i).den * ↑(weightQ m i).num) /
          ↑(commonDenominator m) =
        (↑(weightQ m i).num : ℚ) / ↑(weightQ m i).den := by
          field_simp [hD0, hden0]
          ring
    _ = weightQ m i := Rat.num_div_den _

private lemma sum_multiplicity {m : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m, multiplicity m i = commonDenominator m := by
  apply Nat.cast_injective (R := ℚ)
  have hD0 : (commonDenominator m : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos m).ne'
  apply (div_left_inj' hD0).mp
  rw [Nat.cast_sum, div_self hD0, Finset.sum_div]
  calc
    ∑ i ∈ Finset.range m, (multiplicity m i : ℚ) / commonDenominator m =
        ∑ i ∈ Finset.range m, weightQ m i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact multiplicity_ratio hm (Finset.mem_range.1 hi)
    _ = 1 := sum_weightQ_eq_one hm

private abbrev SampleSigma (m : ℕ) :=
  Σ i : Fin m, Fin (multiplicity m i)

noncomputable def sampleCount (m : ℕ) : ℕ :=
  if hm : 0 < m then Fintype.card (SampleSigma m) else 1

theorem sampleCount_pos (m : ℕ) : 0 < sampleCount m := by
  classical
  unfold sampleCount
  split_ifs with hm
  · rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range]
    rw [sum_multiplicity hm]
    exact commonDenominator_pos m
  · simp

private noncomputable def sampleEquiv (m : ℕ) (hm : 0 < m) :
    Fin (sampleCount m) ≃ SampleSigma m := by
  let e := (Fintype.equivFin (SampleSigma m)).symm
  refine (Fin.castIso ?_).toEquiv.trans e
  rw [sampleCount, dif_pos hm]

noncomputable def start (m : ℕ) (s : Fin (sampleCount m)) : Fin (2 * m + 1) := by
  by_cases hm : 0 < m
  · let a := sampleEquiv m hm s
    exact ⟨a.1.val + 1, by omega⟩
  · exact 0

theorem start_support {m : ℕ} (hm : 0 < m) (s : Fin (sampleCount m)) :
    1 ≤ (start m s).val ∧ (start m s).val ≤ m := by
  classical
  unfold start
  simp only [dif_pos hm]
  let a := sampleEquiv m hm s
  exact ⟨Nat.succ_le_succ (Nat.zero_le _), a.1.isLt⟩

private lemma start_eq_sampleEquiv {m : ℕ} (hm : 0 < m) (s : Fin (sampleCount m)) :
    (start m s).val = ((sampleEquiv m hm) s).1.val + 1 := by
  rw [start]
  simp [hm]

private lemma sum_start_eq_weightQ {m : ℕ} (hm : 0 < m) (f : ℕ → ℚ) :
    (∑ s : Fin (sampleCount m), f (start m s).val) / sampleCount m =
      ∑ i in Finset.range m, weightQ m i * f (i + 1) := by
  classical
  have hsc : sampleCount m = commonDenominator m := by
    rw [sampleCount, dif_pos hm, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_multiplicity hm
  have hsum :
      ∑ s : Fin (sampleCount m), f (start m s).val =
        ∑ i : Fin m, multiplicity m i * f (i.val + 1) := by
    calc
      (∑ s : Fin (sampleCount m), f (start m s).val) =
          ∑ a : SampleSigma m, f (a.1.val + 1) := by
            apply Fintype.sum_equiv (sampleEquiv m hm)
            intro s
            rw [start_eq_sampleEquiv hm]
      _ = ∑ i : Fin m, multiplicity m i * f (i.val + 1) := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        simp
  rw [hsum, hsc]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_div]
  apply Fintype.sum_congr
  intro i
  calc
    ((multiplicity m i : ℚ) * f (i.val + 1)) / commonDenominator m =
        ((multiplicity m i : ℚ) / commonDenominator m) * f (i.val + 1) := by ring
    _ = weightQ m i * f (i.val + 1) := by rw [multiplicity_ratio hm i.isLt]

private lemma sum_start_eq_weightR {m : ℕ} (hm : 0 < m) (f : ℕ → ℝ) :
    (∑ s : Fin (sampleCount m), f (start m s).val) / sampleCount m =
      ∑ i in Finset.range m, (weightQ m i : ℝ) * f (i + 1) := by

  classical
  have hsc : sampleCount m = commonDenominator m := by
    rw [sampleCount, dif_pos hm, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_multiplicity hm
  have hsum :
      ∑ s : Fin (sampleCount m), f (start m s).val =
        ∑ i : Fin m, multiplicity m i * f (i.val + 1) := by
    calc
      (∑ s : Fin (sampleCount m), f (start m s).val) =
          ∑ a : SampleSigma m, f (a.1.val + 1) := by
            apply Fintype.sum_equiv (sampleEquiv m hm)
            intro s
            rw [start_eq_sampleEquiv hm]
      _ = ∑ i : Fin m, multiplicity m i * f (i.val + 1) := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        simp
  rw [hsum, hsc]
  have hratio (i : Fin m) :
      (multiplicity m i : ℝ) / commonDenominator m = (weightQ m i : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (multiplicity_ratio hm i.isLt)
    norm_num at h
    exact h
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_div]
  apply Fintype.sum_congr
  intro i
  calc
    ((multiplicity m i : ℝ) * f (i.val + 1)) / commonDenominator m =
        ((multiplicity m i : ℝ) / commonDenominator m) * f (i.val + 1) := by ring
    _ = (weightQ m i : ℝ) * f (i.val + 1) := by rw [hratio]

noncomputable def maxMass (m j : ℕ) : ℝ :=
  (∑ s : Fin (sampleCount m),
      if (start m s).val ≤ j then
        ((start m s).val : ℝ) / ((j : ℝ) * (j + 1))
      else 0) / sampleCount m

private lemma truncated_momentQ {m j : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m,
        (if i + 1 ≤ j then weightQ m i * ((i + 1 : ℕ) : ℚ) else 0) =
      ∑ i in Finset.range (min m j), weightQ m i * ((i + 1 : ℕ) : ℚ) := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [lt_min_iff, Nat.lt_iff_add_one_le]

private lemma truncated_momentR {m j : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m,
        (if i + 1 ≤ j then (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ) else 0) =
      ∑ i in Finset.range (min m j), (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [lt_min_iff, Nat.lt_iff_add_one_le]

private lemma partial_momentR {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    ∑ i in Finset.range j, (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ) =
      (gammaQ m : ℝ) * (((j : ℝ) * (j + 1)) /
        ((2 * (m : ℝ) - j) * (2 * (m : ℝ) - j + 1))) := by
  exact_mod_cast partial_momentQ (m := m) (j := j) hm hj

private lemma total_momentR {m : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m, (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ) =
      (gammaQ m : ℝ) := by
  exact_mod_cast total_momentQ (m := m) hm

private lemma sum_weightR_eq_one {m : ℕ} (hm : 0 < m) :
    ∑ i in Finset.range m, (weightQ m i : ℝ) = 1 := by
  exact_mod_cast sum_weightQ_eq_one (m := m) hm

private lemma maxMass_of_le {m j : ℕ} (hm : 0 < m) (hj0 : 0 < j) (hjm : j ≤ m) :
    maxMass m j =
      (gammaQ m : ℝ) /
        (((2 * m - j : ℕ) : ℝ) * ((2 * m - j + 1 : ℕ) : ℝ)) := by
  unfold maxMass
  rw [sum_start_eq_weightR hm (fun k =>
    if k ≤ j then (k : ℝ) / ((j : ℝ) * (j + 1)) else 0)]
  have havg :
      ∑ i ∈ Finset.range m, (weightQ m i : ℝ) *
          (if i + 1 ≤ j then ((i + 1 : ℕ) : ℝ) / ((j : ℝ) * (j + 1)) else 0) =
        (∑ i ∈ Finset.range m,
          if i + 1 ≤ j then (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ) else 0) /
            ((j : ℝ) * (j + 1)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i + 1 ≤ j
    · simp [h]
      ring
    · simp [h]
  rw [havg, truncated_momentR hm, min_eq_right hjm, partial_momentR hm hjm]
  have hden : ((j : ℝ) * (j + 1)) ≠ 0 := by positivity
  have hjcast : ((2 * m - j : ℕ) : ℝ) = 2 * (m : ℝ) - j := by
    rw [Nat.cast_sub]
    · push_cast; ring
    · omega
  have hjcast1 : ((2 * m - j + 1 : ℕ) : ℝ) = 2 * (m : ℝ) - j + 1 := by
    rw [Nat.cast_add, hjcast]
    norm_num
  rw [hjcast, hjcast1]
  have hhigh : 0 < 2 * (m : ℝ) - j := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hjR : (j : ℝ) ≤ m := by exact_mod_cast hjm
    linarith
  field_simp [hden, hhigh.ne']
  ring

private lemma maxMass_of_ge {m j : ℕ} (hm : 0 < m) (hmj : m ≤ j) :
    maxMass m j = (gammaQ m : ℝ) / ((j : ℝ) * (j + 1)) := by
  unfold maxMass
  rw [sum_start_eq_weightR hm (fun k =>
    if k ≤ j then (k : ℝ) / ((j : ℝ) * (j + 1)) else 0)]
  have hall (i : ℕ) (hi : i ∈ Finset.range m) : i + 1 ≤ j := by
    exact (Nat.succ_le_of_lt (Finset.mem_range.1 hi)).trans hmj
  calc
    ∑ i ∈ Finset.range m, (weightQ m i : ℝ) *
          (if i + 1 ≤ j then ((i + 1 : ℕ) : ℝ) / ((j : ℝ) * (j + 1)) else 0) =
        (∑ i ∈ Finset.range m,
          (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ)) / ((j : ℝ) * (j + 1)) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            rw [if_pos (hall i hi)]
            ring
    _ = (gammaQ m : ℝ) / ((j : ℝ) * (j + 1)) := by rw [total_momentR hm]

theorem maxMass_symm {m j : ℕ} (hm : 0 < m) (hj : 1 ≤ j) (hjtop : j < 2 * m) :
    maxMass m j = maxMass m (2 * m - j) := by
  by_cases hjm : j ≤ m
  · have hsum : m + j ≤ 2 * m := by omega
    have hkge : m ≤ 2 * m - j := Nat.le_sub_of_add_le hsum
    rw [maxMass_of_le hm hj hjm, maxMass_of_ge hm hkge]
    norm_num
  · have hsmall : 2 * m - j ≤ m := by omega
    have hpos : 0 < 2 * m - j := Nat.sub_pos_of_lt hjtop
    have hjle : j ≤ 2 * m := Nat.le_of_lt hjtop
    have hback : 2 * m - (2 * m - j) = j := Nat.sub_sub_self hjle
    rw [maxMass_of_ge hm (Nat.le_of_lt (lt_of_not_ge hjm)),
        maxMass_of_le hm hpos hsmall]
    rw [hback]
    norm_num

theorem mean_ruin {m : ℕ} (hm : 0 < m) :
    (∑ s : Fin (sampleCount m),
        (((2 * m - (start m s).val : ℕ) : ℝ) / (2 * m : ℕ))) /
        sampleCount m =
      (2 * (m : ℝ)) / (3 * m + 1) := by
  rw [sum_start_eq_weightR hm (fun k =>
    (((2 * m - k : ℕ) : ℝ) / (2 * m : ℕ)))]
  have hsupp (i : ℕ) (hi : i ∈ Finset.range m) : i + 1 ≤ 2 * m := by
    have him : i + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.1 hi)
    have hm2m : m ≤ 2 * m := by omega
    exact him.trans hm2m
  have hcast (i : ℕ) (hi : i ∈ Finset.range m) :
      (((2 * m - (i + 1) : ℕ) : ℝ)) = 2 * (m : ℝ) - (i + 1) := by
    rw [Nat.cast_sub (hsupp i hi)]
    push_cast
    ring
  have hrewrite :
      ∑ i ∈ Finset.range m, (weightQ m i : ℝ) *
          (((2 * m - (i + 1) : ℕ) : ℝ) / (2 * m : ℕ)) =
        ((2 * (m : ℝ)) * (∑ i ∈ Finset.range m, (weightQ m i : ℝ)) -
          ∑ i ∈ Finset.range m, (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ)) /
            (2 * (m : ℝ)) := by
    calc
      ∑ i ∈ Finset.range m, (weightQ m i : ℝ) *
          (((2 * m - (i + 1) : ℕ) : ℝ) / (2 * m : ℕ)) =
          ∑ i ∈ Finset.range m, (weightQ m i : ℝ) *
            ((2 * (m : ℝ) - (i + 1)) / (2 * (m : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hcast i hi]
              push_cast
              rfl
      _ = (∑ i ∈ Finset.range m,
          (weightQ m i : ℝ) * (2 * (m : ℝ) - (i + 1))) / (2 * (m : ℝ)) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ((2 * (m : ℝ)) * (∑ i ∈ Finset.range m, (weightQ m i : ℝ)) -
          ∑ i ∈ Finset.range m, (weightQ m i : ℝ) * ((i + 1 : ℕ) : ℝ)) /
            (2 * (m : ℝ)) := by
              congr 1
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
              push_cast
              ring
  rw [hrewrite, sum_weightR_eq_one hm, total_momentR hm]
  have hgamma : (gammaQ m : ℝ) =
      (2 * (m : ℝ) * (m + 1)) / (3 * (m : ℝ) + 1) := by
    norm_num [gammaQ]
  rw [hgamma]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h3m1 : 3 * (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm0, h3m1]
  ring

end StartDistribution
