import SemiStreamingMatching.Proofs.Blueprint.RandomWalk
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace GamblerWalk

theorem step_val_add_step_val {N : ℕ} (x : State N) :
    (step x false).val + (step x true).val = 2 * x.val := by
  by_cases h0 : x.val = 0
  · simp [step, h0]
  by_cases hN : x.val = N
  · simp [step, h0, hN, Nat.two_mul]
  simp [step, h0, hN]
  omega

theorem position_succ_as_tail {N : ℕ} (start : State N) (moves : ℕ → Bool) (t : ℕ) :
    position start moves (t + 1) =
      position (step start (moves 0)) (fun s => moves (s + 1)) t := by
  induction t generalizing start with
  | zero => rfl
  | succ t ih =>
      change step (position start moves (t + 1)) (moves (t + 1)) =
        step (position (step start (moves 0)) (fun s => moves (s + 1)) t) (moves (t + 1))
      rw [ih]

theorem movesOfWord_piFinSucc_tail {H : ℕ} (b : Bool) (tail : Fin H → Bool) (t : ℕ) :
    movesOfWord ((Equiv.piFinSucc H Bool).symm (b, tail)) (t + 1) =
      movesOfWord tail t := by
  by_cases ht : t < H
  · simp [movesOfWord, blockStream, Equiv.piFinSucc_symm_apply, Fin.cons, ht]
  · have hts : ¬t + 1 < H + 1 := by omega
    simp [movesOfWord, blockStream, ht, hts]

theorem position_word_cons {N H : ℕ} (start : State N) (b : Bool)
    (tail : Fin H → Bool) :
    position start (movesOfWord ((Equiv.piFinSucc H Bool).symm (b, tail))) (H + 1) =
      position (step start b) (movesOfWord tail) H := by
  rw [position_succ_as_tail]
  have hzero : movesOfWord ((Equiv.piFinSucc H Bool).symm (b, tail)) 0 = b := by
    simp [movesOfWord, blockStream, Equiv.piFinSucc_symm_apply]
  rw [hzero]
  apply position_congr_of_lt
  intro t _
  exact movesOfWord_piFinSucc_tail b tail t

theorem sum_position_word (N H : ℕ) (start : State N) :
    ∑ word : Fin H → Bool, (position start (movesOfWord word) H).val =
      2 ^ H * start.val := by
  induction H generalizing start with
  | zero => simp
  | succ H ih =>
      rw [Fintype.sum_equiv (Equiv.piFinSucc H Bool)
        (fun word => (position start (movesOfWord word) (H + 1)).val)
        (fun bt => (position (step start bt.1) (movesOfWord bt.2) H).val)
        (by
          intro word
          have hp := position_word_cons start ((Equiv.piFinSucc H Bool word).1)
            ((Equiv.piFinSucc H Bool word).2)
          rw [(Equiv.piFinSucc H Bool).symm_apply_apply word] at hp
          exact congrArg Fin.val hp)]
      rw [Fintype.sum_prod_type]
      simp_rw [ih]
      rw [Fintype.sum_bool]
      rw [← Nat.mul_add, add_comm, step_val_add_step_val, pow_succ]
      ring

def zeroWords (N H : ℕ) (start : State N) : Finset (Fin H → Bool) :=
  Finset.univ.filter fun word => position start (movesOfWord word) H = 0

def topWords (N H : ℕ) (start : State N) : Finset (Fin H → Bool) :=
  Finset.univ.filter fun word =>
    position start (movesOfWord word) H = (⟨N, by omega⟩ : State N)

def survivorWordFinset (N H : ℕ) (start : State N) : Finset (Fin H → Bool) :=
  Finset.univ.filter fun word => ¬AtBoundary (position start (movesOfWord word) H)

theorem sum_top_indicator (N H : ℕ) (start : State N) :
    ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H = (⟨N, by omega⟩ : State N)
          then N else 0) =
      N * (topWords N H start).card := by
  classical
  calc
    _ = ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H = (⟨N, by omega⟩ : State N)
          then 1 else 0) * N := by
      apply Finset.sum_congr rfl
      intro word _
      split <;> simp_all
    _ = (∑ word : Fin H → Bool,
        if position start (movesOfWord word) H = (⟨N, by omega⟩ : State N)
          then 1 else 0) * N := by rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_boole]; simp [topWords, Nat.mul_comm]

theorem sum_nonzero_indicator (N H : ℕ) (hN : 0 < N) (start : State N) :
    ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H ≠ 0 then N else 0) =
      N * ((topWords N H start).card + (survivorWordFinset N H start).card) := by
  classical
  let nonzero := Finset.univ.filter fun word : Fin H → Bool =>
    position start (movesOfWord word) H ≠ 0
  have hu : topWords N H start ∪ survivorWordFinset N H start = nonzero := by
    ext word
    simp only [topWords, survivorWordFinset, nonzero, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (htop | hsurv)
      · rw [htop]
        intro hzero
        have : N = 0 := congrArg Fin.val hzero
        omega
      · intro hzero
        exact hsurv (by simp [AtBoundary, hzero])
    · intro hnzero
      by_cases htop : position start (movesOfWord word) H =
          (⟨N, by omega⟩ : State N)
      · exact Or.inl htop
      · right
        intro hb
        rcases hb with hz | htopval
        · exact hnzero (Fin.ext hz)
        · exact htop (Fin.ext htopval)
  have hd : Disjoint (topWords N H start) (survivorWordFinset N H start) := by
    apply Finset.disjoint_left.mpr
    intro word htop hsurv
    have htop' := (Finset.mem_filter.mp htop).2
    have hsurv' := (Finset.mem_filter.mp hsurv).2
    exact hsurv' (by simp [AtBoundary, htop'])
  have hcard : nonzero.card =
      (topWords N H start).card + (survivorWordFinset N H start).card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  calc
    _ = ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H ≠ 0 then 1 else 0) * N := by
      apply Finset.sum_congr rfl
      intro word _
      split <;> simp_all
    _ = (∑ word : Fin H → Bool,
        if position start (movesOfWord word) H ≠ 0 then 1 else 0) * N :=
      by rw [Finset.sum_mul]
    _ = nonzero.card * N := by
      rw [Finset.sum_boole]
      rfl
    _ = _ := by rw [hcard, Nat.mul_comm]

theorem top_card_bounds (N H : ℕ) (hN : 0 < N) (start : State N) :
    N * (topWords N H start).card ≤ 2 ^ H * start.val ∧
      2 ^ H * start.val ≤
        N * ((topWords N H start).card + (survivorWordFinset N H start).card) := by
  classical
  rw [← sum_position_word N H start]
  constructor
  · rw [← sum_top_indicator]
    apply Finset.sum_le_sum
    intro word _
    split_ifs with h
    · simp [h]
    · omega
  · rw [← sum_nonzero_indicator N H hN]
    apply Finset.sum_le_sum
    intro word _
    split_ifs with h
    · exact Nat.le_of_lt_succ (position start (movesOfWord word) H).isLt
    · simp_all

theorem sum_position_gap_word (N H : ℕ) (start : State N) :
    (∑ word : Fin H → Bool, (N - (position start (movesOfWord word) H).val)) =
      2 ^ H * (N - start.val) := by
  have hadd :
      (∑ word : Fin H → Bool, (N - (position start (movesOfWord word) H).val)) +
          (∑ word : Fin H → Bool, (position start (movesOfWord word) H).val) =
        ∑ _word : Fin H → Bool, N := by
    calc
      _ = ∑ word : Fin H → Bool,
          ((N - (position start (movesOfWord word) H).val) +
            (position start (movesOfWord word) H).val) :=
        Finset.sum_add_distrib.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro word _
        exact Nat.sub_add_cancel
          (Nat.le_of_lt_succ (position start (movesOfWord word) H).isLt)
  rw [sum_position_word] at hadd
  have hcard : Fintype.card (Fin H → Bool) = 2 ^ H := by simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hadd
  rw [hcard] at hadd
  rw [Nat.mul_sub_left_distrib]
  exact Nat.eq_sub_of_add_eq hadd

theorem sum_zero_indicator (N H : ℕ) (start : State N) :
    ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H = 0 then N else 0) =
      N * (zeroWords N H start).card := by
  classical
  calc
    _ = ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H = 0 then 1 else 0) * N := by
      apply Finset.sum_congr rfl
      intro word _
      split <;> simp_all
    _ = (∑ word : Fin H → Bool,
        if position start (movesOfWord word) H = 0 then 1 else 0) * N := by
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_boole]; simp [zeroWords, Nat.mul_comm]

theorem sum_nontop_indicator (N H : ℕ) (hN : 0 < N) (start : State N) :
    ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H ≠ (⟨N, by omega⟩ : State N)
          then N else 0) =
      N * ((zeroWords N H start).card + (survivorWordFinset N H start).card) := by
  classical
  let nontop := Finset.univ.filter fun word : Fin H → Bool =>
    position start (movesOfWord word) H ≠ (⟨N, by omega⟩ : State N)
  have hu : zeroWords N H start ∪ survivorWordFinset N H start = nontop := by
    ext word
    simp only [zeroWords, survivorWordFinset, nontop, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hzero | hsurv)
      · rw [hzero]
        intro htop
        have : 0 = N := congrArg Fin.val htop
        omega
      · intro htop
        exact hsurv (by simp [AtBoundary, htop])
    · intro hntop
      by_cases hzero : position start (movesOfWord word) H = 0
      · exact Or.inl hzero
      · right
        intro hb
        rcases hb with hz | htopval
        · exact hzero (Fin.ext hz)
        · exact hntop (Fin.ext htopval)
  have hd : Disjoint (zeroWords N H start) (survivorWordFinset N H start) := by
    apply Finset.disjoint_left.mpr
    intro word hzero hsurv
    have hzero' := (Finset.mem_filter.mp hzero).2
    have hsurv' := (Finset.mem_filter.mp hsurv).2
    exact hsurv' (by simp [AtBoundary, hzero'])
  have hcard : nontop.card =
      (zeroWords N H start).card + (survivorWordFinset N H start).card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  calc
    _ = ∑ word : Fin H → Bool,
        (if position start (movesOfWord word) H ≠ (⟨N, by omega⟩ : State N)
          then 1 else 0) * N := by
      apply Finset.sum_congr rfl
      intro word _
      split <;> simp_all
    _ = (∑ word : Fin H → Bool,
        if position start (movesOfWord word) H ≠ (⟨N, by omega⟩ : State N)
          then 1 else 0) * N := by rw [Finset.sum_mul]
    _ = nontop.card * N := by
      rw [Finset.sum_boole]
      rfl
    _ = _ := by rw [hcard, Nat.mul_comm]

theorem zero_card_bounds (N H : ℕ) (hN : 0 < N) (start : State N) :
    N * (zeroWords N H start).card ≤ 2 ^ H * (N - start.val) ∧
      2 ^ H * (N - start.val) ≤
        N * ((zeroWords N H start).card + (survivorWordFinset N H start).card) := by
  classical
  have hgap := sum_position_gap_word N H start
  constructor
  · rw [← sum_zero_indicator]
    rw [← hgap]
    apply Finset.sum_le_sum
    intro word _
    split_ifs with h
    · simp [h]
    · omega
  · rw [← sum_nontop_indicator N H hN]
    rw [← hgap]
    apply Finset.sum_le_sum
    intro word _
    split_ifs with h
    · omega
    · have htop : position start (movesOfWord word) H =
          (⟨N, by omega⟩ : State N) := not_ne_iff.mp h
      simp [htop]

theorem zero_density_lower (N H : ℕ) (hN : 0 < N) (start : State N) :
    (((N - start.val : ℕ) : ℝ) / N) -
        ((survivorWordFinset N H start).card : ℝ) / (2 ^ H : ℕ) ≤
      ((zeroWords N H start).card : ℝ) / (2 ^ H : ℕ) := by
  have hT : (0 : ℝ) < (2 ^ H : ℕ) := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sub_le_iff_le_add, ← add_div, div_le_div_iff hNr hT]
  have hcast : (2 ^ H : ℝ) * (N - start.val : ℕ) ≤
      (N : ℝ) *
        ((zeroWords N H start).card + (survivorWordFinset N H start).card) := by
    exact_mod_cast (zero_card_bounds N H hN start).2
  simpa [mul_comm] using hcast

end GamblerWalk
