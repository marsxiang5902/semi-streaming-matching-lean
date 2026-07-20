import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace GamblerWalk

open scoped BigOperators

abbrev State (N : ℕ) := Fin (N + 1)

def reflect {N : ℕ} (x : State N) : State N :=
  ⟨N - x.1, by omega⟩

@[simp] theorem reflect_val {N : ℕ} (x : State N) :
    (reflect x).1 = N - x.1 := rfl

@[simp] theorem reflect_reflect {N : ℕ} (x : State N) : reflect (reflect x) = x := by
  apply Fin.ext
  simp [reflect]
  omega

@[simp] theorem reflect_zero (N : ℕ) : reflect (0 : State N) = ⟨N, by omega⟩ := by
  apply Fin.ext
  simp [reflect]

@[simp] theorem reflect_top (N : ℕ) : reflect (⟨N, by omega⟩ : State N) = 0 := by
  apply Fin.ext
  simp [reflect]

def step {N : ℕ} (x : State N) (right : Bool) : State N :=
  if h0 : x.1 = 0 then x
  else if hN : x.1 = N then x
  else if right then
    ⟨x.1 + 1, by omega⟩
  else
    ⟨x.1 - 1, by omega⟩

@[simp] theorem step_zero {N : ℕ} (b : Bool) : step (0 : State N) b = 0 := by
  simp [step]

@[simp] theorem step_top {N : ℕ} (b : Bool) :
    step (⟨N, by omega⟩ : State N) b = ⟨N, by omega⟩ := by
  by_cases h : N = 0
  · subst N
    simp [step]
  · simp [step, h]

theorem step_reflect {N : ℕ} (x : State N) (b : Bool) :
    step (reflect x) (!b) = reflect (step x b) := by
  by_cases h0 : x.1 = 0
  · have hx : x = 0 := Fin.ext h0
    rw [hx]
    simp
  by_cases hN : x.1 = N
  · have hx : x = (⟨N, by omega⟩ : State N) := Fin.ext hN
    rw [hx]
    simp
  have hr0 : N - x.1 ≠ 0 := by omega
  have hrN : N - x.1 ≠ N := by omega
  apply Fin.ext
  cases b <;> simp [step, reflect, h0, hN, hr0, hrN] <;> omega

def position {N : ℕ} (start : State N) (moves : ℕ → Bool) : ℕ → State N
  | 0 => start
  | t + 1 => step (position start moves t) (moves t)

@[simp] theorem position_zero {N : ℕ} (start : State N) (moves : ℕ → Bool) :
    position start moves 0 = start := rfl

@[simp] theorem position_succ {N : ℕ} (start : State N) (moves : ℕ → Bool) (t : ℕ) :
    position start moves (t + 1) = step (position start moves t) (moves t) := rfl

theorem position_congr_of_lt {N : ℕ} (start : State N) {moves moves' : ℕ → Bool} {t : ℕ}
    (h : ∀ s < t, moves s = moves' s) :
    position start moves t = position start moves' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [position_succ, position_succ, ih (fun s hs => h s (by omega))]
      rw [h t (by omega)]

theorem position_reflect {N : ℕ} (start : State N) (moves : ℕ → Bool) (t : ℕ) :
    position (reflect start) (fun s => !(moves s)) t = reflect (position start moves t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [position_succ, ih]
      exact step_reflect _ _

def AtBoundary {N : ℕ} (x : State N) : Prop := x.1 = 0 ∨ x.1 = N

instance {N : ℕ} (x : State N) : Decidable (AtBoundary x) := by
  unfold AtBoundary
  infer_instance

@[simp] theorem atBoundary_zero {N : ℕ} : AtBoundary (0 : State N) := Or.inl rfl

@[simp] theorem atBoundary_top {N : ℕ} : AtBoundary (⟨N, by omega⟩ : State N) := Or.inr rfl

@[simp] theorem atBoundary_reflect_iff {N : ℕ} (x : State N) :
    AtBoundary (reflect x) ↔ AtBoundary x := by
  simp only [AtBoundary, reflect_val]
  omega

theorem step_eq_of_atBoundary {N : ℕ} {x : State N} (hx : AtBoundary x) (b : Bool) :
    step x b = x := by
  rcases hx with h | h
  · apply Fin.ext
    simp [step, h]
  · apply Fin.ext
    simp [step, h]

theorem position_add_eq_of_atBoundary {N : ℕ} (start : State N) (moves : ℕ → Bool)
    (t s : ℕ) (ht : AtBoundary (position start moves t)) :
    position start moves (t + s) = position start moves t := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ, position_succ, ih]
      exact step_eq_of_atBoundary ht _

def HitsZeroBy {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, position start moves t = 0

def HitsTopBy {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, position start moves t = ⟨N, by omega⟩

instance {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) :
    Decidable (HitsZeroBy start moves T) := by
  unfold HitsZeroBy
  infer_instance

instance {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) :
    Decidable (HitsTopBy start moves T) := by
  unfold HitsTopBy
  infer_instance

theorem hitsZeroBy_iff_position_eq_zero {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) :
    HitsZeroBy start moves T ↔ position start moves T = 0 := by
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [position_add_eq_of_atBoundary start moves t s (by simpa [hz])]
    exact hz
  · intro h
    exact ⟨T, le_rfl, h⟩

theorem hitsTopBy_iff_position_eq_top {N : ℕ} (start : State N) (moves : ℕ → Bool) (T : ℕ) :
    HitsTopBy start moves T ↔ position start moves T = ⟨N, by omega⟩ := by
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [position_add_eq_of_atBoundary start moves t s (by simpa [hz])]
    exact hz
  · intro h
    exact ⟨T, le_rfl, h⟩

theorem hitsZeroBy_iff_reflected_hitsTopBy {N : ℕ} (start : State N)
    (moves : ℕ → Bool) (T : ℕ) :
    HitsZeroBy start moves T ↔ HitsTopBy (reflect start) (fun s => !(moves s)) T := by
  rw [hitsZeroBy_iff_position_eq_zero, hitsTopBy_iff_position_eq_top,
    position_reflect]
  constructor
  · intro h
    rw [h]
    exact reflect_zero N
  · intro h
    have := congrArg (reflect (N := N)) h
    simpa using this

theorem not_hitsZeroBy_and_reflected_hitsZeroBy {N : ℕ} (hN : 0 < N) (start : State N)
    (moves : ℕ → Bool) (T : ℕ) :
    ¬(HitsZeroBy start moves T ∧ HitsZeroBy (reflect start) (fun s => !(moves s)) T) := by
  rintro ⟨h0, hr0⟩
  have hrN : HitsTopBy (reflect start) (fun s => !(moves s)) T :=
    (hitsZeroBy_iff_reflected_hitsTopBy start moves T).mp h0
  rw [hitsTopBy_iff_position_eq_top] at hrN
  rw [hitsZeroBy_iff_position_eq_zero] at hr0
  have : (0 : State N) = ⟨N, by omega⟩ := hr0.symm.trans hrN
  have : (0 : ℕ) = N := congrArg Fin.val this
  omega

abbrev MoveBlock (N : ℕ) := Fin N → Bool

def allRight (N : ℕ) : MoveBlock N := fun _ => true

def blockStream {N : ℕ} (b : MoveBlock N) (t : ℕ) : Bool :=
  if h : t < N then b ⟨t, h⟩ else false

def runBlock {N : ℕ} (start : State N) (b : MoveBlock N) : State N :=
  position start (blockStream b) N

private theorem position_true_val {N : ℕ} (start : State N) (t : ℕ) :
    (position start (fun _ => true) t).1 =
      if start.1 = 0 then 0 else min (start.1 + t) N := by
  induction t with
  | zero =>
      by_cases h0 : start.1 = 0
      · simp [h0]
      · simp [h0, Nat.min_eq_left (by omega : start.1 ≤ N)]
  | succ t ih =>
      rw [position_succ]
      by_cases hs0 : start.1 = 0
      · have hp0 : position start (fun _ => true) t = 0 := by
          apply Fin.ext
          simpa [hs0] using ih
        simp [hp0, hs0]
      · rw [if_neg hs0]
        by_cases hlt : start.1 + t < N
        · have hpval : (position start (fun _ => true) t).1 = start.1 + t := by
            simpa [hs0, Nat.min_eq_left (Nat.le_of_lt hlt)] using ih
          have hp : position start (fun _ => true) t =
              (⟨start.1 + t, by omega⟩ : State N) := Fin.ext hpval
          have hp0 : (position start (fun _ => true) t).1 ≠ 0 := by omega
          have hpN : (position start (fun _ => true) t).1 ≠ N := by omega
          have hsum0 : start.1 + t ≠ 0 := by omega
          have hsumN : start.1 + t ≠ N := by omega
          rw [hp]
          simp only [step]
          simp only [hsum0, hsumN, Bool.true_eq, ↓reduceIte]
          by_cases hnext : start.1 + (t + 1) ≤ N
          · rw [Nat.min_eq_left hnext]
            simp
            omega
          · rw [Nat.min_eq_right (by omega : N ≤ start.1 + (t + 1))]
            simp
            omega
        · have hpval : (position start (fun _ => true) t).1 = N := by
            simpa [hs0, Nat.min_eq_right (by omega : N ≤ start.1 + t)] using ih
          have hp : position start (fun _ => true) t = (⟨N, by omega⟩ : State N) :=
            Fin.ext hpval
          simp [hp, hs0, Nat.min_eq_right (by omega : N ≤ start.1 + (t + 1))]

theorem atBoundary_runBlock_allRight {N : ℕ} (start : State N) :
    AtBoundary (runBlock start (allRight N)) := by
  have hstream : ∀ t < N, blockStream (allRight N) t = true := by
    intro t ht
    simp [blockStream, allRight, ht]
  have hpos : runBlock start (allRight N) = position start (fun _ => true) N := by
    unfold runBlock
    exact position_congr_of_lt start hstream
  rw [hpos]
  by_cases h0 : start.1 = 0
  · left
    simpa [h0] using position_true_val start N
  · right
    simpa [h0, Nat.min_eq_right (by omega : N ≤ start.1 + N)] using
      position_true_val start N

def runBlocks {N : ℕ} : {k : ℕ} → State N → (Fin k → MoveBlock N) → State N
  | 0, start, _ => start
  | k + 1, start, blocks =>
      runBlocks (runBlock start (blocks 0)) (Fin.tail blocks)

@[simp] theorem runBlocks_zero {N : ℕ} (start : State N) (blocks : Fin 0 → MoveBlock N) :
    runBlocks start blocks = start := rfl

@[simp] theorem runBlocks_succ {N k : ℕ} (start : State N)
    (blocks : Fin (k + 1) → MoveBlock N) :
    runBlocks start blocks = runBlocks (runBlock start (blocks 0)) (Fin.tail blocks) := rfl

theorem runBlock_eq_of_atBoundary {N : ℕ} {start : State N} (h : AtBoundary start)
    (b : MoveBlock N) : runBlock start b = start := by
  unfold runBlock
  simpa using position_add_eq_of_atBoundary start (blockStream b) 0 N (by simpa using h)

theorem runBlocks_eq_of_atBoundary {N k : ℕ} {start : State N} (h : AtBoundary start)
    (blocks : Fin k → MoveBlock N) : runBlocks start blocks = start := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [runBlocks_succ, runBlock_eq_of_atBoundary h]
      exact ih (Fin.tail blocks)

theorem block_ne_allRight_of_runBlocks_not_boundary {N k : ℕ} (start : State N)
    (blocks : Fin k → MoveBlock N) (h : ¬AtBoundary (runBlocks start blocks)) :
    ∀ i, blocks i ≠ allRight N := by
  induction k generalizing start with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hb
        have hfirst : AtBoundary (runBlock start (blocks 0)) := by
          rw [hb]
          exact atBoundary_runBlock_allRight start
        have hfinal : AtBoundary (runBlocks start blocks) := by
          rw [runBlocks_succ, runBlocks_eq_of_atBoundary hfirst]
          exact hfirst
        exact h hfinal
      · have htail : ¬AtBoundary
            (runBlocks (runBlock start (blocks 0)) (Fin.tail blocks)) := by
          simpa only [runBlocks_succ] using h
        exact ih (runBlock start (blocks 0)) (Fin.tail blocks) htail j

abbrev NonRightBlock (N : ℕ) := {b : MoveBlock N // b ≠ allRight N}

abbrev SurvivorWords (N k : ℕ) (start : State N) :=
  {blocks : Fin k → MoveBlock N // ¬AtBoundary (runBlocks start blocks)}

noncomputable def survivorToNonRight {N k : ℕ} (start : State N) :
    SurvivorWords N k start → (Fin k → NonRightBlock N) := fun blocks i =>
  ⟨blocks.1 i, block_ne_allRight_of_runBlocks_not_boundary start blocks.1 blocks.2 i⟩

theorem survivorToNonRight_injective {N k : ℕ} (start : State N) :
    Function.Injective (survivorToNonRight (k := k) start) := by
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg (fun f => (f i).1) h

theorem card_nonRightBlock (N : ℕ) :
    Fintype.card (NonRightBlock N) = 2 ^ N - 1 := by
  classical
  rw [Fintype.card_subtype_compl]
  simp [MoveBlock]

theorem card_survivorWords_le (N k : ℕ) (start : State N) :
    Fintype.card (SurvivorWords N k start) ≤ (2 ^ N - 1) ^ k := by
  classical
  calc
    Fintype.card (SurvivorWords N k start) ≤
        Fintype.card (Fin k → NonRightBlock N) :=
      Fintype.card_le_of_injective (survivorToNonRight start)
        (survivorToNonRight_injective (k := k) start)
    _ = (2 ^ N - 1) ^ k := by simp [card_nonRightBlock]

theorem card_blockWords (N k : ℕ) :
    Fintype.card (Fin k → MoveBlock N) = (2 ^ N) ^ k := by
  simp [MoveBlock]

noncomputable def failureRatio (N : ℕ) : ℝ := ((2 ^ N - 1 : ℕ) : ℝ) / (2 ^ N : ℕ)

theorem failureRatio_nonneg (N : ℕ) : 0 ≤ failureRatio N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem failureRatio_lt_one {N : ℕ} (hN : 0 < N) : failureRatio N < 1 := by
  rw [failureRatio, div_lt_one]
  · exact_mod_cast Nat.sub_lt (by positivity : 0 < 2 ^ N) (by omega : 0 < (1 : ℕ))
  · exact_mod_cast (by positivity : 0 < 2 ^ N)

theorem exists_pow_failure_lt {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, failureRatio N ^ k < ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (failureRatio_nonneg N)
    (failureRatio_lt_one hN)
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨k, hk⟩ := ht ε hε
  refine ⟨k, ?_⟩
  have hp : 0 ≤ failureRatio N ^ k := pow_nonneg (failureRatio_nonneg N) k
  have h := hk k le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp] at h
  exact h

noncomputable def average {N : ℕ} (reward : State N → ℝ) : ℕ → State N → ℝ
  | 0, start => reward start
  | H + 1, start =>
      (average reward H (step start false) + average reward H (step start true)) / 2

theorem average_mono {N H : ℕ} {f g : State N → ℝ} (hfg : ∀ x, f x ≤ g x)
    (start : State N) : average f H start ≤ average g H start := by
  induction H generalizing start with
  | zero => exact hfg start
  | succ H ih =>
      simp only [average]
      gcongr
      · exact ih _
      · exact ih _

theorem average_add {N H : ℕ} (f g : State N → ℝ) (start : State N) :
    average (fun x => f x + g x) H start = average f H start + average g H start := by
  induction H generalizing start with
  | zero => rfl
  | succ H ih =>
      simp only [average, ih]
      ring

noncomputable def zeroPotential {N : ℕ} (x : State N) : ℝ :=
  (N - x.1 : ℕ) / (N : ℝ)

theorem zeroPotential_step_average {N : ℕ} (hN : 0 < N) (x : State N) :
    (zeroPotential (step x false) + zeroPotential (step x true)) / 2 = zeroPotential x := by
  by_cases h0 : x.1 = 0
  · have hx : x = 0 := Fin.ext h0
    rw [hx]
    simp [zeroPotential, hN.ne']
  by_cases htop : x.1 = N
  · have hx : x = (⟨N, by omega⟩ : State N) := Fin.ext htop
    rw [hx]
    simp [zeroPotential, hN.ne']
  have hxpos : 0 < x.1 := by omega
  have hxlt : x.1 < N := by omega
  have hleft : N - (x.1 - 1) = N - x.1 + 1 := by omega
  have hright : N - (x.1 + 1) = N - x.1 - 1 := by omega
  have hdiff : 1 ≤ N - x.1 := by omega
  have hstepL : step x false = (⟨x.1 - 1, by omega⟩ : State N) := by
    simp [step, h0, htop]
  have hstepR : step x true = (⟨x.1 + 1, by omega⟩ : State N) := by
    simp [step, h0, htop]
  rw [hstepL, hstepR]
  simp only [zeroPotential, Fin.val_mk]
  rw [hleft, hright]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hdiff]
  field_simp
  ring

theorem average_zeroPotential {N H : ℕ} (hN : 0 < N) (start : State N) :
    average zeroPotential H start = zeroPotential start := by
  induction H generalizing start with
  | zero => rfl
  | succ H ih =>
      rw [average, ih, ih, zeroPotential_step_average hN]

noncomputable def zeroIndicator {N : ℕ} (x : State N) : ℝ :=
  if x.1 = 0 then 1 else 0

noncomputable def interiorIndicator {N : ℕ} (x : State N) : ℝ :=
  if AtBoundary x then 0 else 1

theorem zeroIndicator_le_zeroPotential {N : ℕ} (hN : 0 < N) (x : State N) :
    zeroIndicator x ≤ zeroPotential x := by
  by_cases h0 : x.1 = 0
  · simp [zeroIndicator, zeroPotential, h0, hN.ne']
  · simp only [zeroIndicator, h0, ↓reduceIte]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem zeroPotential_le_indicator_add {N : ℕ} (hN : 0 < N) (x : State N) :
    zeroPotential x ≤ zeroIndicator x + interiorIndicator x := by
  by_cases h0 : x.1 = 0
  · simp [zeroPotential, zeroIndicator, interiorIndicator, AtBoundary, h0, hN.ne']
  by_cases htop : x.1 = N
  · simp [zeroPotential, zeroIndicator, interiorIndicator, AtBoundary, h0, htop, hN.ne']
  · simp [zeroIndicator, interiorIndicator, AtBoundary, h0, htop, zeroPotential]
    apply (div_le_one (by exact_mod_cast hN)).2
    exact_mod_cast Nat.sub_le N x.1

theorem average_zeroIndicator_le_potential {N H : ℕ} (hN : 0 < N) (start : State N) :
    average zeroIndicator H start ≤ zeroPotential start := by
  rw [← average_zeroPotential hN start]
  exact average_mono (zeroIndicator_le_zeroPotential hN) start

theorem potential_sub_average_interior_le_zero {N H : ℕ} (hN : 0 < N)
    (start : State N) :
    zeroPotential start - average interiorIndicator H start ≤
      average zeroIndicator H start := by
  have h := average_mono (zeroPotential_le_indicator_add hN) (H := H) start
  rw [average_zeroPotential hN, average_add] at h
  linarith

def wordSuccEquiv (H : ℕ) : (Fin (H + 1) → Bool) ≃ Bool × (Fin H → Bool) where
  toFun word := (word 0, Fin.tail word)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv word := Fin.cons_self_tail word
  right_inv pair := by
    rcases pair with ⟨b, tail⟩
    ext <;> simp

theorem position_tail {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) :
    position start moves (H + 1) =
      position (step start (moves 0)) (fun t => moves (t + 1)) H := by
  induction H generalizing start moves with
  | zero => rfl
  | succ H ih =>
      change step (position start moves (H + 1)) (moves (H + 1)) = _
      rw [ih]
      rfl

def movesOfWord {H : ℕ} (word : Fin H → Bool) : ℕ → Bool :=
  blockStream word

@[simp] theorem movesOfWord_apply {H : ℕ} (word : Fin H → Bool) {t : ℕ} (ht : t < H) :
    movesOfWord word t = word ⟨t, ht⟩ := by
  simp [movesOfWord, blockStream, ht]

theorem position_cons_word {N H : ℕ} (start : State N) (head : Bool)
    (tail : Fin H → Bool) :
    position start (movesOfWord (Fin.cons head tail)) (H + 1) =
      position (step start head) (movesOfWord tail) H := by
  rw [position_tail]
  have hhead : movesOfWord (Fin.cons head tail) 0 = head := by
    simp [movesOfWord, blockStream]
  rw [hhead]
  apply position_congr_of_lt
  intro t ht
  rw [movesOfWord_apply _ (by omega : t + 1 < H + 1), movesOfWord_apply _ ht]
  rfl

theorem average_eq_word_sum_div {N H : ℕ} (reward : State N → ℝ) (start : State N) :
    average reward H start =
      (∑ word : (Fin H → Bool), reward (position start (movesOfWord word) H)) / (2 : ℝ) ^ H := by
  induction H generalizing start with
  | zero => simp [average, movesOfWord, blockStream]
  | succ H ih =>
      have hsum :
          (∑ word : (Fin (H + 1) → Bool),
              reward (position start (movesOfWord word) (H + 1))) =
            ∑ pair : (Bool × (Fin H → Bool)),
              reward (position (step start pair.1) (movesOfWord pair.2) H) := by
        apply Fintype.sum_equiv (wordSuccEquiv H)
        intro word
        have hp := position_cons_word start (word 0) (Fin.tail word)
        rw [Fin.cons_self_tail] at hp
        simpa [wordSuccEquiv] using congrArg reward hp
      have hfalse :
          (∑ word : (Fin H → Bool),
              reward (position (step start false) (movesOfWord word) H)) =
            average reward H (step start false) * (2 : ℝ) ^ H := by
        rw [ih]
        field_simp
      have htrue :
          (∑ word : (Fin H → Bool),
              reward (position (step start true) (movesOfWord word) H)) =
            average reward H (step start true) * (2 : ℝ) ^ H := by
        rw [ih]
        field_simp
      rw [average, hsum, Fintype.sum_prod_type, Fintype.sum_bool, htrue, hfalse]
      rw [pow_succ]
      field_simp
      ring

def finiteZeroCount {N H : ℕ} (start : State N) : ℕ :=
  ((Finset.univ : Finset (Fin H → Bool)).filter fun word =>
    HitsZeroBy start (movesOfWord word) H).card

def finiteSurvivorCount {N H : ℕ} (start : State N) : ℕ :=
  ((Finset.univ : Finset (Fin H → Bool)).filter fun word =>
    ¬AtBoundary (position start (movesOfWord word) H)).card

noncomputable def finiteZeroProbability {N H : ℕ} (start : State N) : ℝ :=
  finiteZeroCount (H := H) start / (2 : ℝ) ^ H

noncomputable def finiteSurvivalProbability {N H : ℕ} (start : State N) : ℝ :=
  finiteSurvivorCount (H := H) start / (2 : ℝ) ^ H

theorem finiteZeroProbability_eq_average {N H : ℕ} (start : State N) :
    finiteZeroProbability (H := H) start = average zeroIndicator H start := by
  rw [average_eq_word_sum_div]
  unfold finiteZeroProbability finiteZeroCount
  congr 1
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hh : HitsZeroBy start (movesOfWord word) H
  · have hz : position start (movesOfWord word) H = 0 :=
      (hitsZeroBy_iff_position_eq_zero start (movesOfWord word) H).mp hh
    have hv : (position start (movesOfWord word) H).1 = 0 := congrArg Fin.val hz
    simp [hh, zeroIndicator, hv]
  · have hz : position start (movesOfWord word) H ≠ 0 := fun hzero =>
      hh ((hitsZeroBy_iff_position_eq_zero start (movesOfWord word) H).mpr hzero)
    have hv : (position start (movesOfWord word) H).1 ≠ 0 := by
      intro hval
      exact hz (Fin.ext hval)
    simp [hh, zeroIndicator, hv]

theorem finiteSurvivalProbability_eq_average {N H : ℕ} (start : State N) :
    finiteSurvivalProbability (H := H) start = average interiorIndicator H start := by
  rw [average_eq_word_sum_div]
  unfold finiteSurvivalProbability finiteSurvivorCount
  congr 1
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro word _
  simp [interiorIndicator]

theorem zeroPotential_sub_survival_le_finiteZero {N H : ℕ} (hN : 0 < N)
    (start : State N) :
    zeroPotential start - finiteSurvivalProbability (H := H) start ≤
      finiteZeroProbability (H := H) start := by
  rw [finiteZeroProbability_eq_average, finiteSurvivalProbability_eq_average]
  exact potential_sub_average_interior_le_zero hN start

theorem finiteZero_le_zeroPotential {N H : ℕ} (hN : 0 < N) (start : State N) :
    finiteZeroProbability (H := H) start ≤ zeroPotential start := by
  rw [finiteZeroProbability_eq_average]
  exact average_zeroIndicator_le_potential hN start

theorem finiteSurvivorCount_le (N : ℕ) (start : State N) :
    finiteSurvivorCount (H := N) start ≤ 2 ^ N - 1 := by
  classical
  let survivors :=
    (Finset.univ : Finset (Fin N → Bool)).filter fun word =>
      ¬AtBoundary (position start (movesOfWord word) N)
  have hmissing : allRight N ∉ survivors := by
    simp only [survivors, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    simpa [runBlock, movesOfWord] using atBoundary_runBlock_allRight start
  have hne : survivors ≠ Finset.univ := by
    intro h
    have : allRight N ∈ survivors := by rw [h]; simp
    exact hmissing this
  have hlt : survivors.card < Fintype.card (Fin N → Bool) := by
    exact (Finset.card_lt_iff_ne_univ survivors).2 hne
  change survivors.card ≤ 2 ^ N - 1
  have hcard : Fintype.card (Fin N → Bool) = 2 ^ N := by simp
  omega

theorem atBoundary_allRight_word_of_le {N K : ℕ} (hNK : N ≤ K) (start : State N) :
    AtBoundary (position start (movesOfWord (allRight K)) K) := by
  have hpos : position start (movesOfWord (allRight K)) K =
      position start (fun _ => true) K := by
    apply position_congr_of_lt
    intro t ht
    simp [movesOfWord, blockStream, allRight, ht]
  rw [hpos]
  by_cases h0 : start.1 = 0
  · left
    simpa [h0] using position_true_val start K
  · right
    simpa [h0, Nat.min_eq_right (by omega : N ≤ start.1 + K)] using
      position_true_val start K

theorem finiteSurvivorCount_le_of_boundary_le (N K : ℕ) (hNK : N ≤ K)
    (start : State N) :
    finiteSurvivorCount (H := K) start ≤ 2 ^ K - 1 := by
  classical
  let survivors :=
    (Finset.univ : Finset (Fin K → Bool)).filter fun word =>
      ¬AtBoundary (position start (movesOfWord word) K)
  have hmissing : allRight K ∉ survivors := by
    simp only [survivors, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact atBoundary_allRight_word_of_le hNK start
  have hne : survivors ≠ Finset.univ := by
    intro h
    have : allRight K ∈ survivors := by rw [h]; simp
    exact hmissing this
  have hlt : survivors.card < Fintype.card (Fin K → Bool) :=
    (Finset.card_lt_iff_ne_univ survivors).2 hne
  change survivors.card ≤ 2 ^ K - 1
  have hcard : Fintype.card (Fin K → Bool) = 2 ^ K := by simp
  omega

theorem finiteSurvivalProbability_oneBlock_le_of_boundary_le (N K : ℕ) (hNK : N ≤ K)
    (start : State N) :
    finiteSurvivalProbability (H := K) start ≤ failureRatio K := by
  unfold finiteSurvivalProbability failureRatio
  have hcast : (finiteSurvivorCount (H := K) start : ℝ) ≤ (2 ^ K - 1 : ℕ) := by
    exact_mod_cast finiteSurvivorCount_le_of_boundary_le N K hNK start
  have hpow : (0 : ℝ) < 2 ^ K := by positivity
  have hden : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by norm_num
  rw [hden]
  exact (div_le_div_iff hpow hpow).2 (mul_le_mul_of_nonneg_right hcast hpow.le)

theorem finiteSurvivalProbability_oneBlock_le (N : ℕ) (start : State N) :
    finiteSurvivalProbability (H := N) start ≤ failureRatio N := by
  unfold finiteSurvivalProbability failureRatio
  have hcast : (finiteSurvivorCount (H := N) start : ℝ) ≤ (2 ^ N - 1 : ℕ) := by
    exact_mod_cast finiteSurvivorCount_le N start
  have hpow : (0 : ℝ) < 2 ^ N := by positivity
  have hden : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by norm_num
  rw [hden]
  exact (div_le_div_iff hpow hpow).2 (mul_le_mul_of_nonneg_right hcast hpow.le)

theorem average_eq_zero_of_atBoundary {N H : ℕ} {start : State N} (h : AtBoundary start) :
    average interiorIndicator H start = 0 := by
  induction H generalizing start with
  | zero => simp [average, interiorIndicator, h]
  | succ H ih =>
      simp only [average]
      rw [step_eq_of_atBoundary h, step_eq_of_atBoundary h, ih h]
      norm_num

theorem average_interior_oneBlock_le_mul (N : ℕ) (start : State N) :
    average interiorIndicator N start ≤ failureRatio N * interiorIndicator start := by
  by_cases h : AtBoundary start
  · rw [average_eq_zero_of_atBoundary h]
    simp [interiorIndicator, h]
  · rw [← finiteSurvivalProbability_eq_average]
    simpa [interiorIndicator, h] using finiteSurvivalProbability_oneBlock_le N start

theorem average_interior_block_le_mul_of_boundary_le (N K : ℕ) (hNK : N ≤ K)
    (start : State N) :
    average interiorIndicator K start ≤ failureRatio K * interiorIndicator start := by
  by_cases h : AtBoundary start
  · rw [average_eq_zero_of_atBoundary h]
    simp [interiorIndicator, h]
  · rw [← finiteSurvivalProbability_eq_average]
    simpa [interiorIndicator, h] using
      finiteSurvivalProbability_oneBlock_le_of_boundary_le N K hNK start

theorem average_const_mul {N H : ℕ} (c : ℝ) (f : State N → ℝ) (start : State N) :
    average (fun x => c * f x) H start = c * average f H start := by
  induction H generalizing start with
  | zero => rfl
  | succ H ih =>
      simp only [average, ih]
      ring

theorem average_add_time {N a b : ℕ} (f : State N → ℝ) (start : State N) :
    average f (a + b) start = average (fun x => average f b x) a start := by
  induction a generalizing start with
  | zero => simp [average]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [average]
      rw [ih, ih]

theorem finiteSurvivalProbability_mul_le (N k : ℕ) (start : State N) :
    finiteSurvivalProbability (H := k * N) start ≤ failureRatio N ^ k := by
  rw [finiteSurvivalProbability_eq_average]
  have hstrong : ∀ (k : ℕ) (start : State N),
      average interiorIndicator (k * N) start ≤
        failureRatio N ^ k * interiorIndicator start := by
    intro k
    induction k with
    | zero =>
        intro start
        simp [average]
    | succ k ih =>
        intro start
        rw [Nat.succ_mul, Nat.add_comm, average_add_time]
        calc
          average (fun x => average interiorIndicator (k * N) x) N start ≤
              average (fun x => failureRatio N ^ k * interiorIndicator x) N start :=
            average_mono (fun x => ih x) start
          _ = failureRatio N ^ k * average interiorIndicator N start :=
            average_const_mul _ _ _
          _ ≤ failureRatio N ^ k *
              (failureRatio N * interiorIndicator start) := by
            exact mul_le_mul_of_nonneg_left (average_interior_oneBlock_le_mul N start)
              (pow_nonneg (failureRatio_nonneg N) k)
          _ = failureRatio N ^ (k + 1) * interiorIndicator start := by
            rw [pow_succ]
            ring
  calc
    average interiorIndicator (k * N) start ≤
        failureRatio N ^ k * interiorIndicator start := hstrong k start
    _ ≤ failureRatio N ^ k := by
      have hi : interiorIndicator start ≤ 1 := by
        by_cases h : AtBoundary start <;> simp [interiorIndicator, h]
      nlinarith [pow_nonneg (failureRatio_nonneg N) k]

theorem finiteSurvivalProbability_commonBlock_le (N K k : ℕ) (hNK : N ≤ K)
    (start : State N) :
    finiteSurvivalProbability (H := k * K) start ≤ failureRatio K ^ k := by
  rw [finiteSurvivalProbability_eq_average]
  have hstrong : ∀ (k : ℕ) (start : State N),
      average interiorIndicator (k * K) start ≤
        failureRatio K ^ k * interiorIndicator start := by
    intro k
    induction k with
    | zero =>
        intro start
        simp [average]
    | succ k ih =>
        intro start
        rw [Nat.succ_mul, Nat.add_comm, average_add_time]
        calc
          average (fun x => average interiorIndicator (k * K) x) K start ≤
              average (fun x => failureRatio K ^ k * interiorIndicator x) K start :=
            average_mono (fun x => ih x) start
          _ = failureRatio K ^ k * average interiorIndicator K start :=
            average_const_mul _ _ _
          _ ≤ failureRatio K ^ k *
              (failureRatio K * interiorIndicator start) := by
            exact mul_le_mul_of_nonneg_left
              (average_interior_block_le_mul_of_boundary_le N K hNK start)
              (pow_nonneg (failureRatio_nonneg K) k)
          _ = failureRatio K ^ (k + 1) * interiorIndicator start := by
            rw [pow_succ]
            ring
  calc
    average interiorIndicator (k * K) start ≤
        failureRatio K ^ k * interiorIndicator start := hstrong k start
    _ ≤ failureRatio K ^ k := by
      have hi : interiorIndicator start ≤ 1 := by
        by_cases h : AtBoundary start <;> simp [interiorIndicator, h]
      nlinarith [pow_nonneg (failureRatio_nonneg K) k]

theorem exists_horizon_survival_lt {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (start : State N) :
    ∃ H : ℕ, finiteSurvivalProbability (H := H) start < ε := by
  obtain ⟨k, hk⟩ := exists_pow_failure_lt hN hε
  exact ⟨k * N, lt_of_le_of_lt (finiteSurvivalProbability_mul_le N k start) hk⟩

theorem exists_finiteZero_gt_potential_sub {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (start : State N) :
    ∃ H : ℕ, zeroPotential start - ε < finiteZeroProbability (H := H) start := by
  obtain ⟨H, hH⟩ := exists_horizon_survival_lt hN hε start
  refine ⟨H, ?_⟩
  have hlo := zeroPotential_sub_survival_le_finiteZero (H := H) hN start
  linarith

def maxPositionUpTo {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) : ℕ :=
  (Finset.range (H + 1)).sup fun t => (position start moves t).1

theorem position_le_maxPositionUpTo {N : ℕ} (start : State N) (moves : ℕ → Bool)
    {H t : ℕ} (ht : t ≤ H) :
    (position start moves t).1 ≤ maxPositionUpTo start moves H := by
  unfold maxPositionUpTo
  exact Finset.le_sup (f := fun s => (position start moves s).1) (by simp; omega)

theorem maxPositionUpTo_le {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) :
    maxPositionUpTo start moves H ≤ N := by
  unfold maxPositionUpTo
  apply Finset.sup_le
  intro t ht
  exact Nat.le_of_lt_succ (position start moves t).2

theorem exists_position_eq_maxPositionUpTo {N : ℕ} (start : State N) (moves : ℕ → Bool)
    (H : ℕ) :
    ∃ t ≤ H, (position start moves t).1 = maxPositionUpTo start moves H := by
  have hne : (Finset.range (H + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨t, ht, heq⟩ :=
    Finset.exists_mem_eq_sup (s := Finset.range (H + 1)) hne
      (fun s => (position start moves s).1)
  exact ⟨t, by simp at ht; omega, heq.symm⟩

noncomputable def firstMaxTime {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) : ℕ :=
  Nat.find (exists_position_eq_maxPositionUpTo start moves H)

theorem firstMaxTime_le {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) :
    firstMaxTime start moves H ≤ H :=
  (Nat.find_spec (exists_position_eq_maxPositionUpTo start moves H)).1

theorem position_firstMaxTime {N : ℕ} (start : State N) (moves : ℕ → Bool) (H : ℕ) :
    (position start moves (firstMaxTime start moves H)).1 = maxPositionUpTo start moves H :=
  (Nat.find_spec (exists_position_eq_maxPositionUpTo start moves H)).2

theorem firstMaxTime_minimal {N : ℕ} (start : State N) (moves : ℕ → Bool) (H t : ℕ)
    (ht : t ≤ H) (hpos : (position start moves t).1 = maxPositionUpTo start moves H) :
    firstMaxTime start moves H ≤ t := by
  exact Nat.find_min' (exists_position_eq_maxPositionUpTo start moves H) ⟨ht, hpos⟩

def ZeroWithMax {N H : ℕ} (start : State N) (j : ℕ) (word : Fin H → Bool) : Prop :=
  HitsZeroBy start (movesOfWord word) H ∧
    maxPositionUpTo start (movesOfWord word) H = j

instance {N H : ℕ} (start : State N) (j : ℕ) (word : Fin H → Bool) :
    Decidable (ZeroWithMax start j word) := by
  unfold ZeroWithMax
  infer_instance

def liftState {N : ℕ} (x : State N) : State (N + 1) :=
  ⟨x.1, by omega⟩

@[simp] theorem liftState_val {N : ℕ} (x : State N) : (liftState x).1 = x.1 := rfl

@[simp] theorem liftState_zero {N : ℕ} : liftState (0 : State N) = 0 := by
  apply Fin.ext
  rfl

theorem step_liftState_of_ne_top {N : ℕ} (x : State N) (b : Bool) (hx : x.1 ≠ N) :
    step (liftState x) b = liftState (step x b) := by
  by_cases h0 : x.1 = 0
  · have hstate : x = 0 := Fin.ext h0
    rw [hstate]
    simp [liftState]
  have hsuccTop : x.1 ≠ N + 1 := by omega
  apply Fin.ext
  cases b <;> simp [step, liftState, h0, hx, hsuccTop]

private theorem position_ne_top_of_final_zero {N H t : ℕ} (hN : 0 < N)
    (start : State N) (moves : ℕ → Bool) (ht : t ≤ H)
    (hzero : position start moves H = 0) :
    (position start moves t).1 ≠ N := by
  intro htopval
  have htop : position start moves t = (⟨N, by omega⟩ : State N) := Fin.ext htopval
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le ht
  have hstay := position_add_eq_of_atBoundary start moves t s (by simp [htop])
  rw [← hs, hzero, htop] at hstay
  have : (0 : ℕ) = N := congrArg Fin.val hstay
  omega

theorem position_liftState_eq_of_final_zero {N H : ℕ} (hN : 0 < N)
    (start : State N) (moves : ℕ → Bool)
    (hzero : position start moves H = 0) {t : ℕ} (ht : t ≤ H) :
    position (liftState start) moves t = liftState (position start moves t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [position_succ, position_succ, ih (by omega)]
      exact step_liftState_of_ne_top _ _
        (position_ne_top_of_final_zero hN start moves (by omega) hzero)

theorem position_liftState_eq_of_avoids {N H : ℕ} (start : State N) (moves : ℕ → Bool)
    (havoid : ∀ t ≤ H, (position (liftState start) moves t).1 ≠ N)
    {t : ℕ} (ht : t ≤ H) :
    position (liftState start) moves t = liftState (position start moves t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev := ih (by omega)
      have hsmall : (position start moves t).1 ≠ N := by
        intro hs
        apply havoid t (by omega)
        rw [hprev]
        exact hs
      rw [position_succ, position_succ, hprev]
      exact step_liftState_of_ne_top _ _ hsmall

def finiteZeroWords (N H : ℕ) (start : State N) : Finset (Fin H → Bool) :=
  Finset.univ.filter fun word => HitsZeroBy start (movesOfWord word) H

@[simp] theorem card_finiteZeroWords (N H : ℕ) (start : State N) :
    (finiteZeroWords N H start).card = finiteZeroCount (H := H) start := rfl

theorem finiteZeroWords_subset_succ {N H : ℕ} (hN : 0 < N) (start : State N) :
    finiteZeroWords N H start ⊆ finiteZeroWords (N + 1) H (liftState start) := by
  intro word hword
  have hzero : position start (movesOfWord word) H = 0 :=
    (hitsZeroBy_iff_position_eq_zero start (movesOfWord word) H).mp
      (Finset.mem_filter.mp hword).2
  have hlift := position_liftState_eq_of_final_zero hN start (movesOfWord word) hzero le_rfl
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (hitsZeroBy_iff_position_eq_zero (liftState start) (movesOfWord word) H).mpr
  rw [hlift, hzero]
  exact liftState_zero

def finiteMaxZeroWords (j H : ℕ) (start : State j) : Finset (Fin H → Bool) :=
  finiteZeroWords (j + 1) H (liftState start) \ finiteZeroWords j H start

noncomputable def finiteMaxZeroProbability {j H : ℕ} (start : State j) : ℝ :=
  (finiteMaxZeroWords j H start).card / (2 : ℝ) ^ H

theorem finiteMaxZeroProbability_eq_sub {j H : ℕ} (hj : 0 < j) (start : State j) :
    finiteMaxZeroProbability (H := H) start =
      finiteZeroProbability (H := H) (liftState start) -
        finiteZeroProbability (H := H) start := by
  have hsub := finiteZeroWords_subset_succ (H := H) hj start
  unfold finiteMaxZeroProbability finiteMaxZeroWords finiteZeroProbability
  rw [Finset.card_sdiff hsub]
  rw [Nat.cast_sub (Finset.card_le_card hsub)]
  simp only [card_finiteZeroWords]
  ring

theorem zeroPotential_lift_sub {j : ℕ} (hj : 0 < j) (start : State j) :
    zeroPotential (liftState start) - zeroPotential start =
      (start.1 : ℝ) / ((j : ℝ) * (j + 1)) := by
  have hs : start.1 ≤ j := Nat.le_of_lt_succ start.2
  have hs' : start.1 ≤ j + 1 := by omega
  unfold zeroPotential
  simp only [liftState_val]
  rw [Nat.cast_sub hs, Nat.cast_sub hs']
  push_cast
  field_simp
  ring

theorem maxZeroProbability_lower {j H : ℕ} (hj : 0 < j) (start : State j) :
    (start.1 : ℝ) / ((j : ℝ) * (j + 1)) -
        finiteSurvivalProbability (H := H) (liftState start) ≤
      finiteMaxZeroProbability (H := H) start := by
  have hlarge := zeroPotential_sub_survival_le_finiteZero (H := H) (by omega : 0 < j + 1)
    (liftState start)
  have hsmall := finiteZero_le_zeroPotential (H := H) hj start
  rw [finiteMaxZeroProbability_eq_sub hj, ← zeroPotential_lift_sub hj start]
  linarith

theorem mem_finiteMaxZeroWords_iff_zeroWithMax {j H : ℕ} (hj : 0 < j)
    (start : State j) (word : Fin H → Bool) :
    word ∈ finiteMaxZeroWords j H start ↔ ZeroWithMax (liftState start) j word := by
  classical
  let moves := movesOfWord word
  constructor
  · intro hmem
    rcases Finset.mem_sdiff.mp hmem with ⟨hlargeMem, hsmallMem⟩
    have hlargeHit : HitsZeroBy (liftState start) moves H :=
      (Finset.mem_filter.mp hlargeMem).2
    have hlargeZero : position (liftState start) moves H = 0 :=
      (hitsZeroBy_iff_position_eq_zero (liftState start) moves H).mp hlargeHit
    have hreach : ∃ t ≤ H, (position (liftState start) moves t).1 = j := by
      by_contra hno
      have havoid : ∀ t ≤ H, (position (liftState start) moves t).1 ≠ j := by
        intro t ht heq
        exact hno ⟨t, ht, heq⟩
      have hcouple := position_liftState_eq_of_avoids start moves havoid (t := H) le_rfl
      have hsmallZero : position start moves H = 0 := by
        apply Fin.ext
        have := congrArg Fin.val hcouple
        simpa [hlargeZero] using this.symm
      apply hsmallMem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (hitsZeroBy_iff_position_eq_zero start moves H).mpr hsmallZero
    have hmax_le : maxPositionUpTo (liftState start) moves H ≤ j := by
      unfold maxPositionUpTo
      apply Finset.sup_le
      intro t ht
      have htH : t ≤ H := by simp at ht; omega
      have hne : (position (liftState start) moves t).1 ≠ j + 1 :=
        position_ne_top_of_final_zero (by omega : 0 < j + 1) (liftState start) moves htH
          hlargeZero
      have hbound := (position (liftState start) moves t).2
      omega
    have hmax_ge : j ≤ maxPositionUpTo (liftState start) moves H := by
      obtain ⟨t, ht, heq⟩ := hreach
      calc
        j = (position (liftState start) moves t).1 := heq.symm
        _ ≤ maxPositionUpTo (liftState start) moves H :=
          position_le_maxPositionUpTo (liftState start) moves ht
    exact ⟨hlargeHit, le_antisymm hmax_le hmax_ge⟩
  · rintro ⟨hlargeHit, hmax⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlargeHit⟩
    · intro hsmallMem
      have hsmallHit : HitsZeroBy start (movesOfWord word) H :=
        (Finset.mem_filter.mp hsmallMem).2
      have hsmallZero : position start (movesOfWord word) H = 0 :=
        (hitsZeroBy_iff_position_eq_zero start (movesOfWord word) H).mp hsmallHit
      obtain ⟨t, ht, heq⟩ :=
        exists_position_eq_maxPositionUpTo (liftState start) (movesOfWord word) H
      have hcouple := position_liftState_eq_of_final_zero hj start (movesOfWord word)
        hsmallZero ht
      have hsmallTop : (position start (movesOfWord word) t).1 = j := by
        have hvals := congrArg Fin.val hcouple
        rw [heq, hmax] at hvals
        simpa using hvals.symm
      exact (position_ne_top_of_final_zero hj start (movesOfWord word) ht hsmallZero) hsmallTop

theorem firstMaxTime_of_mem_finiteMaxZeroWords {j H : ℕ} (hj : 0 < j)
    (start : State j) {word : Fin H → Bool} (hword : word ∈ finiteMaxZeroWords j H start) :
    (position (liftState start) (movesOfWord word)
      (firstMaxTime (liftState start) (movesOfWord word) H)).1 = j := by
  rw [position_firstMaxTime]
  exact (mem_finiteMaxZeroWords_iff_zeroWithMax hj start word).mp hword |>.2

end GamblerWalk
