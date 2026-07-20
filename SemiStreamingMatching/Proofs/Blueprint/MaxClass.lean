import SemiStreamingMatching.Proofs.Blueprint.RandomWalk
import SemiStreamingMatching.Proofs.Blueprint.RandomWalkCounting

open scoped BigOperators

namespace GamblerWalk

def widenState {K N : ℕ} (hKN : K ≤ N) (x : State K) : State N :=
  ⟨x.1, by omega⟩

@[simp] theorem widenState_val {K N : ℕ} (hKN : K ≤ N) (x : State K) :
    (widenState hKN x).1 = x.1 := rfl

@[simp] theorem widenState_zero {K N : ℕ} (hKN : K ≤ N) :
    widenState hKN (0 : State K) = 0 := by
  apply Fin.ext
  rfl

theorem step_widenState_of_lt {K N : ℕ} (hKN : K ≤ N) (x : State K) (b : Bool)
    (hx : x.1 < K) :
    step (widenState hKN x) b = widenState hKN (step x b) := by
  by_cases h0 : x.1 = 0
  · have hstate : x = 0 := Fin.ext h0
    subst x
    simp [widenState]
  have hxK : x.1 ≠ K := by omega
  have hxN : x.1 ≠ N := by omega
  apply Fin.ext
  cases b <;> simp [step, widenState, h0, hxK, hxN]

private theorem position_widenState_of_small_below {K N H : ℕ} (hKN : K ≤ N)
    (start : State K) (moves : ℕ → Bool)
    (hbelow : ∀ t ≤ H, (position start moves t).1 < K) {t : ℕ} (ht : t ≤ H) :
    position (widenState hKN start) moves t = widenState hKN (position start moves t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [position_succ, position_succ, ih (by omega)]
      exact step_widenState_of_lt hKN _ _ (hbelow t (by omega))

private theorem position_widenState_of_large_below {K N H : ℕ} (hKN : K ≤ N)
    (start : State K) (moves : ℕ → Bool)
    (hbelow : ∀ t ≤ H, (position (widenState hKN start) moves t).1 < K)
    {t : ℕ} (ht : t ≤ H) :
    position (widenState hKN start) moves t = widenState hKN (position start moves t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev := ih (by omega)
      have hsmall : (position start moves t).1 < K := by
        have hlarge := hbelow t (by omega)
        rw [hprev] at hlarge
        exact hlarge
      rw [position_succ, position_succ, hprev]
      exact step_widenState_of_lt hKN _ _ hsmall

theorem zeroWithMax_widenState_iff {K N H j : ℕ} (hKN : K ≤ N) (hjK : j < K)
    (start : State K) (word : Fin H → Bool) :
    ZeroWithMax (widenState hKN start) j word ↔ ZeroWithMax start j word := by
  let moves := movesOfWord word
  constructor
  · rintro ⟨hzero, hmax⟩
    have hbelow : ∀ t ≤ H, (position (widenState hKN start) moves t).1 < K := by
      intro t ht
      have hle := position_le_maxPositionUpTo (widenState hKN start) moves ht
      rw [hmax] at hle
      omega
    have hcouple : ∀ {t : ℕ}, t ≤ H →
        position (widenState hKN start) moves t =
          widenState hKN (position start moves t) := by
      intro t ht
      exact position_widenState_of_large_below hKN start moves hbelow ht
    have hfinalLarge : position (widenState hKN start) moves H = 0 :=
      (hitsZeroBy_iff_position_eq_zero _ _ _).mp hzero
    have hfinalSmall : position start moves H = 0 := by
      apply Fin.ext
      have hvals := congrArg Fin.val (hcouple (t := H) le_rfl)
      rw [hfinalLarge] at hvals
      simpa using hvals.symm
    refine ⟨(hitsZeroBy_iff_position_eq_zero _ _ _).mpr hfinalSmall, ?_⟩
    unfold maxPositionUpTo at hmax ⊢
    rw [← hmax]
    apply Finset.sup_congr rfl
    intro t ht
    have htH : t ≤ H := by simp at ht; omega
    exact (congrArg Fin.val (hcouple htH)).symm
  · rintro ⟨hzero, hmax⟩
    have hbelow : ∀ t ≤ H, (position start moves t).1 < K := by
      intro t ht
      have hle := position_le_maxPositionUpTo start moves ht
      rw [hmax] at hle
      omega
    have hcouple : ∀ {t : ℕ}, t ≤ H →
        position (widenState hKN start) moves t =
          widenState hKN (position start moves t) := by
      intro t ht
      exact position_widenState_of_small_below hKN start moves hbelow ht
    have hfinalSmall : position start moves H = 0 :=
      (hitsZeroBy_iff_position_eq_zero _ _ _).mp hzero
    have hfinalLarge : position (widenState hKN start) moves H = 0 := by
      rw [hcouple le_rfl, hfinalSmall]
      exact widenState_zero hKN
    refine ⟨(hitsZeroBy_iff_position_eq_zero _ _ _).mpr hfinalLarge, ?_⟩
    unfold maxPositionUpTo at hmax ⊢
    rw [← hmax]
    apply Finset.sup_congr rfl
    intro t ht
    have htH : t ≤ H := by simp at ht; omega
    exact congrArg Fin.val (hcouple htH)

def stateAtBarrier {N j : ℕ} (start : State N) (hstart : start.1 ≤ j) : State j :=
  ⟨start.1, by omega⟩

@[simp] theorem stateAtBarrier_val {N j : ℕ} (start : State N) (hstart : start.1 ≤ j) :
    (stateAtBarrier start hstart).1 = start.1 := rfl

def ambientMaxZeroWords (N H : ℕ) (start : State N) (j : ℕ) : Finset (Fin H → Bool) :=
  Finset.univ.filter fun word => ZeroWithMax start j word

noncomputable def ambientMaxZeroProbability {N H : ℕ} (start : State N) (j : ℕ) : ℝ :=
  (ambientMaxZeroWords N H start j).card / (2 : ℝ) ^ H

theorem ambientMaxZeroWords_eq_finiteMaxZeroWords {N H j : ℕ} (hj : 0 < j) (hjN : j < N)
    (start : State N) (hstart : start.1 ≤ j) :
    ambientMaxZeroWords N H start j =
      finiteMaxZeroWords j H (stateAtBarrier start hstart) := by
  classical
  let small := stateAtBarrier start hstart
  have hbarrier : j + 1 ≤ N := by omega
  have hwiden : widenState hbarrier (liftState small) = start := by
    apply Fin.ext
    rfl
  ext word
  rw [mem_finiteMaxZeroWords_iff_zeroWithMax hj small word]
  simp only [ambientMaxZeroWords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hwiden, zeroWithMax_widenState_iff hbarrier (by omega : j < j + 1)]

theorem ambientMaxZeroProbability_eq_finiteMaxZeroProbability {N H j : ℕ}
    (hj : 0 < j) (hjN : j < N) (start : State N) (hstart : start.1 ≤ j) :
    ambientMaxZeroProbability (H := H) start j =
      finiteMaxZeroProbability (H := H) (stateAtBarrier start hstart) := by
  unfold ambientMaxZeroProbability finiteMaxZeroProbability
  rw [ambientMaxZeroWords_eq_finiteMaxZeroWords hj hjN start hstart]

theorem ambientMaxZeroProbability_eq_zero_of_lt_start {N H j : ℕ} (start : State N)
    (hstart : j < start.1) :
    ambientMaxZeroProbability (H := H) start j = 0 := by
  have hempty : ambientMaxZeroWords N H start j = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro word hword
    have hmax := (Finset.mem_filter.mp hword).2.2
    have hle := position_le_maxPositionUpTo start (movesOfWord word) (H := H) (t := 0) (by omega)
    simp only [position_zero] at hle
    omega
  simp [ambientMaxZeroProbability, hempty]

theorem maxZeroProbability_upper {j H : ℕ} (hj : 0 < j) (start : State j) :
    finiteMaxZeroProbability (H := H) start ≤
      (start.1 : ℝ) / ((j : ℝ) * (j + 1)) +
        finiteSurvivalProbability (H := H) start := by
  have hlarge := finiteZero_le_zeroPotential (H := H) (by omega : 0 < j + 1)
    (liftState start)
  have hsmall := zeroPotential_sub_survival_le_finiteZero (H := H) hj start
  rw [finiteMaxZeroProbability_eq_sub hj, ← zeroPotential_lift_sub hj start]
  linarith

theorem ambientMaxZeroProbability_approx {N K k j : ℕ} (hNK : N ≤ K) (hj : 0 < j)
    (hjN : j < N) (start : State N) :
    |ambientMaxZeroProbability (H := k * K) start j -
        (if start.1 ≤ j then (start.1 : ℝ) / ((j : ℝ) * (j + 1)) else 0)| ≤
      failureRatio K ^ k := by
  by_cases hs : start.1 ≤ j
  · rw [if_pos hs, ambientMaxZeroProbability_eq_finiteMaxZeroProbability hj hjN start hs]
    let small := stateAtBarrier start hs
    have hjK : j ≤ K := by omega
    have hj1K : j + 1 ≤ K := by omega
    have hsurvSmall : finiteSurvivalProbability (H := k * K) small ≤
        failureRatio K ^ k :=
      finiteSurvivalProbability_commonBlock_le j K k hjK small
    have hsurvLarge : finiteSurvivalProbability (H := k * K) (liftState small) ≤
        failureRatio K ^ k :=
      finiteSurvivalProbability_commonBlock_le (j + 1) K k hj1K (liftState small)
    apply abs_le.mpr
    constructor
    · have hlo := maxZeroProbability_lower (H := k * K) hj small
      dsimp [small] at hlo ⊢
      linarith
    · have hup := maxZeroProbability_upper (H := k * K) hj small
      dsimp [small] at hup ⊢
      linarith
  · rw [if_neg hs, ambientMaxZeroProbability_eq_zero_of_lt_start start (by omega)]
    simpa using pow_nonneg (failureRatio_nonneg K) k

theorem average_ambientMaxZeroProbability_approx {S : Type*} [Fintype S] [Nonempty S]
    {N K k j : ℕ} (hNK : N ≤ K) (hj : 0 < j) (hjN : j < N)
    (start : S → State N) :
    |((∑ s, ambientMaxZeroProbability (H := k * K) (start s) j) / Fintype.card S -
        (∑ s, if (start s).1 ≤ j then
          ((start s).1 : ℝ) / ((j : ℝ) * (j + 1)) else 0) / Fintype.card S)| ≤
      failureRatio K ^ k := by
  let δ := failureRatio K ^ k
  let actual : S → ℝ := fun s => ambientMaxZeroProbability (H := k * K) (start s) j
  let target : S → ℝ := fun s => if (start s).1 ≤ j then
    ((start s).1 : ℝ) / ((j : ℝ) * (j + 1)) else 0
  change |(∑ s, actual s) / Fintype.card S - (∑ s, target s) / Fintype.card S| ≤ δ
  have hpoint (s : S) : |actual s - target s| ≤ δ :=
    ambientMaxZeroProbability_approx hNK hj hjN (start s)
  have hlower (s : S) : target s - δ ≤ actual s := by
    have := (abs_le.mp (hpoint s)).1
    linarith
  have hupper (s : S) : actual s ≤ target s + δ := by
    have := (abs_le.mp (hpoint s)).2
    linarith
  have hcard : (0 : ℝ) < Fintype.card S := by positivity
  have hsumLower : (∑ s, (target s - δ)) ≤ ∑ s, actual s :=
    Finset.sum_le_sum fun s _ => hlower s
  have hsumUpper : (∑ s, actual s) ≤ ∑ s, (target s + δ) :=
    Finset.sum_le_sum fun s _ => hupper s
  apply abs_le.mpr
  constructor
  · rw [← sub_div]
    apply (le_div_iff hcard).2
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsumLower
    nlinarith
  · rw [← sub_div]
    apply (div_le_iff hcard).2
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsumUpper
    nlinarith

end GamblerWalk
