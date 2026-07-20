import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open scoped BigOperators

namespace Formal.Streaming

structure FiniteDist (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteDist

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

noncomputable def expect (P : FiniteDist Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

noncomputable def prob (P : FiniteDist Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  ∑ ω with E ω, P.mass ω

@[simp] theorem expect_const (P : FiniteDist Ω) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.sum_mass]

theorem expect_add (P : FiniteDist Ω) (X Y : Ω → ℝ) :
    P.expect (fun ω => X ω + Y ω) = P.expect X + P.expect Y := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_smul (P : FiniteDist Ω) (c : ℝ) (X : Ω → ℝ) :
    P.expect (fun ω => c * X ω) = c * P.expect X := by
  simp only [expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_nonneg (P : FiniteDist Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) :
    0 ≤ P.expect X := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (P.mass_nonneg ω) (hX ω)

theorem expect_mono (P : FiniteDist Ω) {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    P.expect X ≤ P.expect Y := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hXY ω) (P.mass_nonneg ω)

@[simp] theorem prob_true (P : FiniteDist Ω) : P.prob (fun _ => True) = 1 := by
  simp [prob, P.sum_mass]

@[simp] theorem prob_false (P : FiniteDist Ω) : P.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_nonneg (P : FiniteDist Ω) (E : Ω → Prop) [DecidablePred E] :
    0 ≤ P.prob E :=
  Finset.sum_nonneg fun ω _ => P.mass_nonneg ω

theorem prob_le_one (P : FiniteDist Ω) (E : Ω → Prop) [DecidablePred E] :
    P.prob E ≤ 1 := by
  rw [← P.sum_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun ω _ _ => P.mass_nonneg ω)

theorem prob_mono (P : FiniteDist Ω) {E F : Ω → Prop}
    [DecidablePred E] [DecidablePred F] (hEF : ∀ ω, E ω → F ω) :
    P.prob E ≤ P.prob F := by
  unfold prob
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hEF ω hω
  · intro ω _ _
    exact P.mass_nonneg ω

theorem prob_compl (P : FiniteDist Ω) (E : Ω → Prop) [DecidablePred E] :
    P.prob (fun ω => ¬ E ω) = 1 - P.prob E := by
  classical
  rw [prob, prob, ← P.sum_mass]
  have hpart := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset Ω)) E P.mass
  rw [← hpart]
  ring

theorem prob_eq_expect_indicator (P : FiniteDist Ω) (E : Ω → Prop) [DecidablePred E] :
    P.prob E = P.expect (fun ω => if E ω then 1 else 0) := by
  classical
  unfold prob expect
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite]
  simp

theorem union_bound (P : FiniteDist Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] :
    P.prob (fun ω => E ω ∨ F ω) ≤ P.prob E + P.prob F := by
  rw [prob_eq_expect_indicator, prob_eq_expect_indicator, prob_eq_expect_indicator,
    ← P.expect_add]
  apply P.expect_mono
  intro ω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]

theorem markov (P : FiniteDist Ω) (X : Ω → ℝ) (t : ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (ht : 0 < t) :
    P.prob (fun ω => t ≤ X ω) ≤ P.expect X / t := by
  have hmul : P.prob (fun ω => t ≤ X ω) * t ≤ P.expect X := by
    unfold prob expect
    calc
      (∑ ω with t ≤ X ω, P.mass ω) * t
          = ∑ ω with t ≤ X ω, P.mass ω * t := by rw [Finset.sum_mul]
      _ ≤ ∑ ω with t ≤ X ω, P.mass ω * X ω := by
        apply Finset.sum_le_sum
        intro ω hω
        exact mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hω).2 (P.mass_nonneg ω)
      _ ≤ ∑ ω, P.mass ω * X ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω _ _
        exact mul_nonneg (P.mass_nonneg ω) (hX ω)
  exact (le_div_iff ht).2 hmul

noncomputable def map (P : FiniteDist Ω) (f : Ω → A) : FiniteDist A where
  mass := by
    classical
    exact fun a => ∑ ω with f ω = a, P.mass ω
  mass_nonneg := by
    classical
    intro a
    exact Finset.sum_nonneg fun ω _ => P.mass_nonneg ω
  sum_mass := by
    classical
    simpa using (Finset.sum_fiberwise (Finset.univ : Finset Ω) f P.mass).trans P.sum_mass

@[simp] theorem map_mass [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A) (a : A) :
    (P.map f).mass a = ∑ ω with f ω = a, P.mass ω := by
  classical
  unfold map
  apply Finset.sum_congr
  · ext ω
    simp
  · intro ω _
    rfl

theorem expect_map (P : FiniteDist Ω) (f : Ω → A) (X : A → ℝ) :
    (P.map f).expect X = P.expect (X ∘ f) := by
  classical
  unfold expect
  calc
    (∑ a, (P.map f).mass a * X a)
        = ∑ a, ∑ ω with f ω = a, P.mass ω * X (f ω) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [map_mass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ω hω
          rw [(Finset.mem_filter.1 hω).2]
    _ = ∑ ω, P.mass ω * X (f ω) :=
      Finset.sum_fiberwise (Finset.univ : Finset Ω) f (fun ω => P.mass ω * X (f ω))
    _ = _ := rfl

theorem prob_map (P : FiniteDist Ω) (f : Ω → A) (E : A → Prop) [DecidablePred E] :
    (P.map f).prob E = P.prob (fun ω => E (f ω)) := by
  classical
  unfold prob
  calc
    (∑ a with E a, (P.map f).mass a)
        = ∑ a in Finset.univ.filter E, ∑ ω with f ω = a, P.mass ω := by
          apply Finset.sum_congr rfl
          intro a _
          rfl
    _ = ∑ ω in Finset.univ.filter (fun ω => f ω ∈ Finset.univ.filter E), P.mass ω :=
      Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset Ω) (Finset.univ.filter E) f P.mass
    _ = ∑ ω with E (f ω), P.mass ω := by simp

noncomputable def conditionMap [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A) (a : A)
    (ha : 0 < (P.map f).mass a) : FiniteDist Ω where
  mass ω := if f ω = a then P.mass ω / (P.map f).mass a else 0
  mass_nonneg ω := by
    dsimp
    split
    · exact div_nonneg (P.mass_nonneg ω) ha.le
    · exact le_rfl
  sum_mass := by
    classical
    dsimp
    simp_rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_div, ← map_mass]
    apply div_self
    simpa only [map_mass] using ha.ne'

@[simp] theorem conditionMap_mass [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A)
    (a : A) (ha : 0 < (P.map f).mass a) (ω : Ω) :
    (P.conditionMap f a ha).mass ω =
      if f ω = a then P.mass ω / (P.map f).mass a else 0 := rfl

noncomputable def conditional [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A) (a : A) :
    FiniteDist Ω :=
  if ha : 0 < (P.map f).mass a then P.conditionMap f a ha else P

theorem conditional_eq_conditionMap [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A)
    (a : A) (ha : 0 < (P.map f).mass a) :
    P.conditional f a = P.conditionMap f a ha := by
  unfold conditional
  rw [dif_pos ha]

theorem conditional_eq_self_of_mass_zero [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A)
    (a : A) (ha : (P.map f).mass a = 0) : P.conditional f a = P := by
  unfold conditional
  rw [dif_neg (by linarith)]

theorem conditional_prob [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A)
    (a : A) (ha : 0 < (P.map f).mass a) (E : Ω → Prop) [DecidablePred E] :
    (P.conditional f a).prob E =
      P.prob (fun ω => E ω ∧ f ω = a) / (P.map f).mass a := by
  rw [P.conditional_eq_conditionMap f a ha]
  unfold prob
  simp_rw [conditionMap_mass]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_div]
  congr 2
  ext ω
  simp [and_comm, and_left_comm]

theorem sum_map_mass_mul_conditional_prob [DecidableEq A] (P : FiniteDist Ω)
    (f : Ω → A) (E : Ω → Prop) [DecidablePred E] :
    (∑ a, (P.map f).mass a * (P.conditional f a).prob E) = P.prob E := by
  letI : DecidableEq Ω := Classical.decEq Ω
  calc
    (∑ a, (P.map f).mass a * (P.conditional f a).prob E) =
        ∑ a, P.prob (fun ω => E ω ∧ f ω = a) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha0 : (P.map f).mass a = 0
      · rw [ha0, zero_mul]
        symm
        unfold prob
        apply Finset.sum_eq_zero
        intro ω hω
        have hmem : ω ∈ (Finset.univ : Finset Ω).filter (fun ω => f ω = a) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Finset.mem_filter.1 hω).2.2
        have hle : P.mass ω ≤
            ∑ x with f x = a, P.mass x :=
          Finset.single_le_sum (fun x _ => P.mass_nonneg x) hmem
        have hsum : (∑ x with f x = a, P.mass x) = 0 := by
          rw [← map_mass]
          exact ha0
        rw [hsum] at hle
        exact le_antisymm hle (P.mass_nonneg ω)
      · have ha : 0 < (P.map f).mass a :=
          lt_of_le_of_ne ((P.map f).mass_nonneg a) (Ne.symm ha0)
        rw [P.conditional_prob f a ha E]
        exact mul_div_cancel₀ _ ha0
    _ = P.prob E := by
      unfold prob
      have h := Finset.sum_fiberwise ((Finset.univ : Finset Ω).filter E) f P.mass
      rw [← h]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr
      · ext ω
        simp [and_comm, and_left_comm]
      · intro ω _
        rfl

noncomputable def condProb (P : FiniteDist Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] : ℝ :=
  P.prob (fun ω => E ω ∧ F ω) / P.prob F

theorem condProb_mul (P : FiniteDist Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] :
    P.condProb E F * P.prob F = P.prob (fun ω => E ω ∧ F ω) := by
  unfold condProb
  by_cases hF : P.prob F = 0
  · rw [hF, div_zero, mul_zero]
    apply le_antisymm (P.prob_nonneg _)
    rw [← hF]
    exact P.prob_mono fun _ h => h.2
  · exact div_mul_cancel₀ _ hF

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDist Ω where
  mass _ := 1 / Fintype.card Ω
  mass_nonneg _ := by positivity
  sum_mass := by
    simp [Fintype.card_ne_zero]

@[simp] theorem uniform_mass (Ω : Type*) [Fintype Ω] [Nonempty Ω] (ω : Ω) :
    (uniform Ω).mass ω = 1 / Fintype.card Ω := rfl

theorem uniform_expect (Ω : Type*) [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    (uniform Ω).expect X = (∑ ω, X ω) / Fintype.card Ω := by
  unfold expect uniform
  simp only [one_div, inv_mul_eq_div, Finset.sum_div]

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) [DecidablePred E] :
    (uniform Ω).prob E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  unfold prob uniform
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat]
  ring

end FiniteDist

abbrev FixedCard (E : Type*) [Fintype E] (q : ℕ) :=
  {D : Finset E // D.card = q}

namespace FixedCard

variable {E : Type*} [Fintype E]

@[simp] theorem card (q : ℕ) : Fintype.card (FixedCard E q) = Nat.choose (Fintype.card E) q :=
  Fintype.card_finset_len q

theorem nonempty (q : ℕ) (hq : q ≤ Fintype.card E) : Nonempty (FixedCard E q) := by
  classical
  have hq' : q ≤ (Finset.univ : Finset E).card := by simpa using hq
  obtain ⟨D, hD⟩ := (Finset.powersetCard_nonempty.mpr hq')
  exact ⟨⟨D, (Finset.mem_powersetCard.mp hD).2⟩⟩

noncomputable def uniform (q : ℕ) (hq : q ≤ Fintype.card E) : FiniteDist (FixedCard E q) := by
  letI : Nonempty (FixedCard E q) := nonempty q hq
  exact FiniteDist.uniform (FixedCard E q)

@[simp] theorem uniform_mass (q : ℕ) (hq : q ≤ Fintype.card E) (D : FixedCard E q) :
    (uniform q hq).mass D = 1 / Nat.choose (Fintype.card E) q := by
  letI : Nonempty (FixedCard E q) := nonempty q hq
  simp [uniform, card]

theorem deletion_card (q : ℕ) (D : FixedCard E q) : D.1.card = q := D.2

theorem expected_deletion_card (q : ℕ) (hq : q ≤ Fintype.card E) :
    (uniform q hq).expect (fun D => (D.1.card : ℝ)) = q := by
  simp [deletion_card, FiniteDist.expect_const]

end FixedCard

end Formal.Streaming
