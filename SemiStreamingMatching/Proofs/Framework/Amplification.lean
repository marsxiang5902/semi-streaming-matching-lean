import SemiStreamingMatching.Proofs.Framework.Framework
import SemiStreamingMatching.Proofs.Framework.HardnessMonotonicity
import SemiStreamingMatching.Definitions.MatchingAlgorithm
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

namespace Formal.Streaming

open scoped BigOperators

namespace RandomizedOnePassAlgorithm

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

noncomputable def largestIndex {k : ℕ} (hk : 0 < k)
    (f : Fin k → Finset (Edge L R)) : Fin k :=
  Classical.choose
    (Finset.exists_max_image Finset.univ (fun i ↦ (f i).card)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩)

theorem largestIndex_mem {k : ℕ} (hk : 0 < k)
    (f : Fin k → Finset (Edge L R)) :
    largestIndex hk f ∈ (Finset.univ : Finset (Fin k)) :=
    (Classical.choose_spec
    (Finset.exists_max_image Finset.univ (fun i ↦ (f i).card)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩)).1

theorem card_le_largestIndex {k : ℕ} (hk : 0 < k)
    (f : Fin k → Finset (Edge L R)) (i : Fin k) :
    (f i).card ≤ (f (largestIndex hk f)).card := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ (fun j ↦ (f j).card)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ i)

noncomputable def parallelRepeat (A : RandomizedOnePassAlgorithm L R)
    (k : ℕ) (hk : 0 < k) : RandomizedOnePassAlgorithm L R where
  State := Fin k → A.State
  stateFintype := inferInstance
  Seed := Fin k → A.Seed
  seedFintype := inferInstance
  seedNonempty := inferInstance
  init ξ i := A.init (ξ i)
  step ξ state edge i := A.step (ξ i) (state i) edge
  output ξ state :=
    let answers := fun i ↦ A.output (ξ i) (state i)
    answers (largestIndex hk answers)

@[simp]
theorem parallelRepeat_runFrom_apply (A : RandomizedOnePassAlgorithm L R)
    (k : ℕ) (hk : 0 < k) (ξ : Fin k → A.Seed)
    (state : Fin k → A.State) (xs : List (Edge L R)) (i : Fin k) :
    ((parallelRepeat A k hk).fixSeed ξ).runFrom state xs i =
      (A.fixSeed (ξ i)).runFrom (state i) xs := by
  induction xs generalizing state with
  | nil => rfl
  | cons edge xs ih =>
      change
        ((parallelRepeat A k hk).fixSeed ξ).runFrom
            (fun j ↦ A.step (ξ j) (state j) edge) xs i =
          (A.fixSeed (ξ i)).runFrom (A.step (ξ i) (state i) edge) xs
      exact ih (fun j ↦ A.step (ξ j) (state j) edge)

@[simp]
theorem repeat_fixSeed_result_apply (A : RandomizedOnePassAlgorithm L R)
    (k : ℕ) (hk : 0 < k) (ξ : Fin k → A.Seed)
    (xs : List (Edge L R)) (i : Fin k) :
    ((parallelRepeat A k hk).fixSeed ξ).run xs i =
      (A.fixSeed (ξ i)).run xs := by
  exact parallelRepeat_runFrom_apply A k hk ξ
    ((parallelRepeat A k hk).fixSeed ξ).init xs i

theorem repeat_result_eq_coordinate (A : RandomizedOnePassAlgorithm L R)
    (k : ℕ) (hk : 0 < k) (ξ : Fin k → A.Seed)
    (xs : List (Edge L R)) :
    ∃ i : Fin k,
      ((parallelRepeat A k hk).fixSeed ξ).result xs =
        (A.fixSeed (ξ i)).result xs := by
  let f : Fin k → Finset (Edge L R) :=
    fun i ↦ (A.fixSeed (ξ i)).result xs
  refine ⟨largestIndex hk f, ?_⟩
  change
    A.output (ξ (largestIndex hk fun i ↦
      A.output (ξ i) (((parallelRepeat A k hk).fixSeed ξ).run xs i)))
      (((parallelRepeat A k hk).fixSeed ξ).run xs (largestIndex hk fun i ↦
        A.output (ξ i) (((parallelRepeat A k hk).fixSeed ξ).run xs i))) =
    A.output (ξ (largestIndex hk f))
      ((A.fixSeed (ξ (largestIndex hk f))).run xs)
  simp_rw [repeat_fixSeed_result_apply]
  rfl

theorem coordinate_result_card_le_repeat (A : RandomizedOnePassAlgorithm L R)
    (k : ℕ) (hk : 0 < k) (ξ : Fin k → A.Seed)
    (xs : List (Edge L R)) (i : Fin k) :
    ((A.fixSeed (ξ i)).result xs).card ≤
      (((parallelRepeat A k hk).fixSeed ξ).result xs).card := by
  let f : Fin k → Finset (Edge L R) :=
    fun j ↦ (A.fixSeed (ξ j)).result xs
  have hmax := card_le_largestIndex (L := L) (R := R) hk f i
  have hout : ((parallelRepeat A k hk).fixSeed ξ).result xs =
      f (largestIndex hk f) := by
    change
      A.output (ξ (largestIndex hk fun j ↦
        A.output (ξ j) (((parallelRepeat A k hk).fixSeed ξ).run xs j)))
        (((parallelRepeat A k hk).fixSeed ξ).run xs (largestIndex hk fun j ↦
          A.output (ξ j) (((parallelRepeat A k hk).fixSeed ξ).run xs j))) = _
    simp_rw [repeat_fixSeed_result_apply]
    rfl
  simpa [f, hout] using hmax

theorem repeat_alwaysFeasible {A : RandomizedOnePassAlgorithm L R}
    (hA : A.AlwaysFeasible) (k : ℕ) (hk : 0 < k) :
    (parallelRepeat A k hk).AlwaysFeasible := by
  intro ξ G σ
  obtain ⟨i, hi⟩ := repeat_result_eq_coordinate A k hk ξ σ.order
  rw [hi]
  exact hA (ξ i) G σ

theorem repeat_succeeds_of_coordinate {A : RandomizedOnePassAlgorithm L R}
    (hA : A.AlwaysFeasible) (k : ℕ) (hk : 0 < k)
    (ξ : Fin k → A.Seed) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) (i : Fin k)
    (hi : (A.fixSeed (ξ i)).SucceedsOn ρ G σ) :
    ((parallelRepeat A k hk).fixSeed ξ).SucceedsOn ρ G σ := by
  refine ⟨repeat_alwaysFeasible hA k hk ξ G σ, ?_⟩
  exact hi.2.trans (by
    exact_mod_cast coordinate_result_card_le_repeat A k hk ξ σ.order i)

theorem parallelRepeat_usesBits {A : RandomizedOnePassAlgorithm L R}
    {s : ℕ} (hA : A.UsesBits s) (k : ℕ) (hk : 0 < k) :
    (parallelRepeat A k hk).UsesBits (k * s) := by
  apply Function.Embedding.nonempty_of_card_le
  obtain ⟨encoding⟩ := hA
  have hcard : Fintype.card A.State ≤ 2 ^ s := by
    simpa [BitString] using Fintype.card_le_of_embedding encoding
  simp only [parallelRepeat, Fintype.card_fun, Fintype.card_fin,
    BitString, Nat.card_eq_fintype_card]
  calc
    Fintype.card A.State ^ k ≤ (2 ^ s) ^ k := Nat.pow_le_pow_left hcard k
    _ = 2 ^ (s * k) := (pow_mul 2 s k).symm
    _ = 2 ^ (k * s) := by rw [Nat.mul_comm]

noncomputable def unsuccessfulSeeds (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) : Finset A.Seed := by
  classical
  exact Finset.univ.filter fun ξ => ¬(A.fixSeed ξ).SucceedsOn ρ G σ

@[simp]
theorem mem_unsuccessfulSeeds_iff (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) (ξ : A.Seed) :
    ξ ∈ A.unsuccessfulSeeds ρ G σ ↔
      ¬(A.fixSeed ξ).SucceedsOn ρ G σ := by
  classical
  simp [unsuccessfulSeeds]

theorem successful_add_unsuccessful_card
    (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    (A.successfulSeeds ρ G σ).card +
      (A.unsuccessfulSeeds ρ G σ).card = Fintype.card A.Seed := by
  classical
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset A.Seed))
    (p := fun ξ => (A.fixSeed ξ).SucceedsOn ρ G σ)

noncomputable def allCoordinatesFailSeeds
    (A : RandomizedOnePassAlgorithm L R) (k : ℕ)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    Finset (Fin k → A.Seed) := by
  classical
  exact Finset.univ.filter fun ξ =>
    ∀ i, ξ i ∈ A.unsuccessfulSeeds ρ G σ

theorem allCoordinatesFailSeeds_card
    (A : RandomizedOnePassAlgorithm L R) (k : ℕ)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    (A.allCoordinatesFailSeeds k ρ G σ).card =
      (A.unsuccessfulSeeds ρ G σ).card ^ k := by
  classical
  let Bad := {ξ : A.Seed // ξ ∈ A.unsuccessfulSeeds ρ G σ}
  let AllBad := {ξ : Fin k → A.Seed //
    ∀ i, ξ i ∈ A.unsuccessfulSeeds ρ G σ}
  let e : (Fin k → Bad) ≃ AllBad :=
    { toFun := fun ξ ↦ show AllBad from
        ⟨fun i ↦ (ξ i).1, fun i ↦ (ξ i).2⟩
      invFun := fun ξ i ↦ show Bad from ⟨ξ.1 i, ξ.2 i⟩
      left_inv := by
        intro ξ
        funext i
        exact Subtype.ext rfl
      right_inv := by
        intro ξ
        apply Subtype.ext
        funext i
        rfl }
  calc
    (A.allCoordinatesFailSeeds k ρ G σ).card = Fintype.card AllBad := by
      simpa [allCoordinatesFailSeeds, AllBad] using
        (Fintype.card_coe (A.allCoordinatesFailSeeds k ρ G σ)).symm
    _ = Fintype.card (Fin k → Bad) := (Fintype.card_congr e).symm
    _ = Fintype.card Bad ^ k := by simp
    _ = (A.unsuccessfulSeeds ρ G σ).card ^ k := by
      congr 1
      simpa [Bad] using
        (Fintype.card_coe (A.unsuccessfulSeeds ρ G σ))

theorem repeat_unsuccessfulSeeds_subset_allCoordinatesFail
    {A : RandomizedOnePassAlgorithm L R} (hA : A.AlwaysFeasible)
    (k : ℕ) (hk : 0 < k) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    (parallelRepeat A k hk).unsuccessfulSeeds ρ G σ ⊆
      A.allCoordinatesFailSeeds k ρ G σ := by
  classical
  intro ξ hξ
  rw [mem_unsuccessfulSeeds_iff] at hξ
  rw [allCoordinatesFailSeeds, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun i ↦ ?_⟩
  rw [mem_unsuccessfulSeeds_iff]
  intro hi
  exact hξ (repeat_succeeds_of_coordinate hA k hk ξ ρ G σ i hi)

theorem repeat_unsuccessfulSeeds_card_le_pow
    {A : RandomizedOnePassAlgorithm L R} (hA : A.AlwaysFeasible)
    (k : ℕ) (hk : 0 < k) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    ((parallelRepeat A k hk).unsuccessfulSeeds ρ G σ).card ≤
      (A.unsuccessfulSeeds ρ G σ).card ^ k := by
  rw [← A.allCoordinatesFailSeeds_card k ρ G σ]
  exact Finset.card_le_card
    (repeat_unsuccessfulSeeds_subset_allCoordinatesFail hA k hk ρ G σ)

noncomputable def failureProbability (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) : ℚ :=
  (A.unsuccessfulSeeds ρ G σ).card / Fintype.card A.Seed

theorem failureProbability_nonneg (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    0 ≤ A.failureProbability ρ G σ := by
  unfold failureProbability
  positivity

theorem successProbability_add_failureProbability
    (A : RandomizedOnePassAlgorithm L R)
    (ρ : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    A.successProbability ρ G σ + A.failureProbability ρ G σ = 1 := by
  rw [successProbability, failureProbability, ← add_div]
  have hcard := A.successful_add_unsuccessful_card ρ G σ
  have hcast :
      ((A.successfulSeeds ρ G σ).card : ℚ) +
        (A.unsuccessfulSeeds ρ G σ).card = Fintype.card A.Seed := by
    exact_mod_cast hcard
  rw [hcast]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem failureProbability_le_of_successProbability
    (A : RandomizedOnePassAlgorithm L R)
    (ρ ε : ℚ) (G : BipartiteGraph L R) (σ : G.EdgeStream)
    (h : 1 - ε ≤ A.successProbability ρ G σ) :
    A.failureProbability ρ G σ ≤ ε := by
  linarith [A.successProbability_add_failureProbability ρ G σ]

theorem parallelRepeat_failureProbability_le_pow
    {A : RandomizedOnePassAlgorithm L R} (hA : A.AlwaysFeasible)
    (k : ℕ) (hk : 0 < k) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    (parallelRepeat A k hk).failureProbability ρ G σ ≤
      (A.failureProbability ρ G σ) ^ k := by
  have hbad := repeat_unsuccessfulSeeds_card_le_pow hA k hk ρ G σ
  have hseed : Fintype.card (Fin k → A.Seed) =
      Fintype.card A.Seed ^ k := by simp
  rw [failureProbability, failureProbability]
  change
    (((parallelRepeat A k hk).unsuccessfulSeeds ρ G σ).card : ℚ) /
        Fintype.card (Fin k → A.Seed) ≤
      (((A.unsuccessfulSeeds ρ G σ).card : ℚ) /
        Fintype.card A.Seed) ^ k
  rw [hseed, div_pow]
  push_cast
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hbad
  · positivity

theorem parallelRepeat_successProbability_ge
    {A : RandomizedOnePassAlgorithm L R} (hA : A.AlwaysFeasible)
    (k : ℕ) (hk : 0 < k) (ρ ε : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream)
    (hsuccess : 1 - ε ≤ A.successProbability ρ G σ) :
    1 - ε ^ k ≤
      (parallelRepeat A k hk).successProbability ρ G σ := by
  have hfail : A.failureProbability ρ G σ ≤ ε :=
    A.failureProbability_le_of_successProbability ρ ε G σ hsuccess
  have hfailPow : (A.failureProbability ρ G σ) ^ k ≤ ε ^ k := by
    exact pow_le_pow_left (A.failureProbability_nonneg ρ G σ) hfail k
  have hamp := parallelRepeat_failureProbability_le_pow hA k hk ρ G σ
  have hsum := (parallelRepeat A k hk).successProbability_add_failureProbability
    ρ G σ
  linarith

end RandomizedOnePassAlgorithm

theorem IsSemiStreamingSpace.const_mul {space : ℕ → ℕ}
    (hspace : IsSemiStreamingSpace space) (k : ℕ) (hk : 0 < k) :
    IsSemiStreamingSpace (fun n ↦ k * space n) := by
  rcases hspace with ⟨c, exponent, n₀, hc, hbound⟩
  refine ⟨k * c, exponent, n₀, Nat.mul_pos hk hc, fun n hn ↦ ?_⟩
  calc
    k * space n ≤ k * (c * n * (Nat.log 2 n + 1) ^ exponent) :=
      Nat.mul_le_mul_left k (hbound n hn)
    _ = (k * c) * n * (Nat.log 2 n + 1) ^ exponent := by ring

namespace SemiStreamingMatchingAlgorithm

noncomputable def parallelRepeat (A : SemiStreamingMatchingAlgorithm)
    (k : ℕ) (hk : 0 < k) : SemiStreamingMatchingAlgorithm where
  algorithm n := A.algorithm n |>.parallelRepeat k hk
  spaceBits n := k * A.spaceBits n
  usesBits n := RandomizedOnePassAlgorithm.parallelRepeat_usesBits
    (A.usesBits n) k hk
  semiStreamingSpace := A.semiStreamingSpace.const_mul k hk
  alwaysFeasible n := RandomizedOnePassAlgorithm.repeat_alwaysFeasible
    (A.alwaysFeasible n) k hk

end SemiStreamingMatchingAlgorithm

namespace SequentialBlueprintHardFamily

noncomputable def raiseApproximation {B : SimpleProperBlueprint}
    (F : SequentialBlueprintHardFamily B) (rho' : ℚ)
    (h : F.approximation ≤ rho') : SequentialBlueprintHardFamily B where
  size := F.size
  hostMultiplicity := F.hostMultiplicity
  distribution := F.distribution
  approximation := rho'
  successThreshold := F.successThreshold
  communicationScale := F.communicationScale
  spaceDomination := F.spaceDomination
  communicationHard := by
    intro k s hs
    exact (F.communicationHard k s hs).mono_approximation h

theorem exists_positive_pow_lt {ε γ : ℚ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hγ : 0 < γ) :
    ∃ copies : ℕ, 0 < copies ∧ ε ^ copies < γ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hγ hε1
  refine ⟨n + 1, by omega, ?_⟩
  apply lt_of_le_of_lt _ hn
  rw [pow_succ]
  nlinarith [pow_nonneg hε0 n]

def HasAmplifiableParameters {B : SimpleProperBlueprint}
    (F : SequentialBlueprintHardFamily B) (ε γ : ℚ) : Prop :=
  F.approximation = blueprintRatioRat B + ε ∧
    F.successThreshold ≤ 1 - γ

theorem blueprint_to_semiStreaming_lower_bound_amplified
    {B : SimpleProperBlueprint} {ε γ : ℚ}
    (F : SequentialBlueprintHardFamily B)
    (hF : F.HasAmplifiableParameters ε γ)
    (copies : ℕ) (hcopies : 0 < copies) (hpower : ε ^ copies < γ)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.distribution k).Sample,
        (A.algorithm (F.size k)).successProbability
            (blueprintRatioRat B + ε)
            ((F.distribution k).input x).graph
            ((F.distribution k).input x).stream ≤ 1 - ε := by
  let A' := A.parallelRepeat copies hcopies
  obtain ⟨k₀, hk₀⟩ := F.defeats_semiStreaming A'.toSemiStreamingAlgorithm
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨x, hx⟩ := hk₀ k hk
  refine ⟨x, ?_⟩
  rcases hF with ⟨happrox, hthreshold⟩
  rw [happrox] at hx
  by_contra hbase
  have hbase' : 1 - ε <
      (A.algorithm (F.size k)).successProbability
        (blueprintRatioRat B + ε)
        ((F.distribution k).input x).graph
        ((F.distribution k).input x).stream := lt_of_not_ge hbase
  have hamp := RandomizedOnePassAlgorithm.parallelRepeat_successProbability_ge
    (A.alwaysFeasible (F.size k)) copies hcopies
    (blueprintRatioRat B + ε) ε
    ((F.distribution k).input x).graph
    ((F.distribution k).input x).stream hbase'.le
  have hx' :
      (A'.algorithm (F.size k)).successProbability
          (blueprintRatioRat B + ε)
          ((F.distribution k).input x).graph
          ((F.distribution k).input x).stream ≤ 1 - γ :=
    hx.trans hthreshold
  change 1 - ε ^ copies ≤
      (A'.algorithm (F.size k)).successProbability
        (blueprintRatioRat B + ε)
        ((F.distribution k).input x).graph
        ((F.distribution k).input x).stream at hamp
  have hstrict : 1 - γ < 1 - ε ^ copies := by linarith
  exact (not_lt_of_ge hx') (hstrict.trans_le hamp)

theorem blueprint_to_semiStreaming_lower_bound_amplified_of_unit
    {B : SimpleProperBlueprint} {ε γ : ℚ}
    (F : SequentialBlueprintHardFamily B)
    (hF : F.HasAmplifiableParameters ε γ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hγ : 0 < γ)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.distribution k).Sample,
        (A.algorithm (F.size k)).successProbability
            (blueprintRatioRat B + ε)
            ((F.distribution k).input x).graph
            ((F.distribution k).input x).stream ≤ 1 - ε := by
  obtain ⟨copies, hcopies, hpower⟩ :=
    exists_positive_pow_lt hε0 hε1 hγ
  exact F.blueprint_to_semiStreaming_lower_bound_amplified hF
    copies hcopies hpower A

theorem blueprint_to_semiStreaming_lower_bound_amplified_general
    {B : SimpleProperBlueprint} {ε γ target : ℚ}
    (F : SequentialBlueprintHardFamily B)
    (hF : F.HasAmplifiableParameters ε γ)
    (htarget0 : 0 < target) (htarget1 : target < 1) (hγ : 0 < γ)
    (A : SemiStreamingMatchingAlgorithm) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ x : (F.distribution k).Sample,
        (A.algorithm (F.size k)).successProbability
            (blueprintRatioRat B + ε)
            ((F.distribution k).input x).graph
            ((F.distribution k).input x).stream ≤ target := by

  obtain ⟨copies, hcopies, hpower⟩ :=
    exists_positive_pow_lt (by linarith : (0 : ℚ) ≤ 1 - target)
      (by linarith : (1 : ℚ) - target < 1) hγ
  let A' := A.parallelRepeat copies hcopies
  obtain ⟨k₀, hk₀⟩ := F.defeats_semiStreaming A'.toSemiStreamingAlgorithm
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨x, hx⟩ := hk₀ k hk
  refine ⟨x, ?_⟩
  rcases hF with ⟨happrox, hthreshold⟩
  rw [happrox] at hx
  by_contra hbase
  have hbase' : target <
      (A.algorithm (F.size k)).successProbability
        (blueprintRatioRat B + ε)
        ((F.distribution k).input x).graph
        ((F.distribution k).input x).stream := lt_of_not_ge hbase
  have hamp := RandomizedOnePassAlgorithm.parallelRepeat_successProbability_ge
    (A.alwaysFeasible (F.size k)) copies hcopies
    (blueprintRatioRat B + ε) (1 - target)
    ((F.distribution k).input x).graph
    ((F.distribution k).input x).stream (by linarith)
  have hx' :
      (A'.algorithm (F.size k)).successProbability
          (blueprintRatioRat B + ε)
          ((F.distribution k).input x).graph
          ((F.distribution k).input x).stream ≤ 1 - γ :=
    hx.trans hthreshold
  change 1 - (1 - target) ^ copies ≤
      (A'.algorithm (F.size k)).successProbability
        (blueprintRatioRat B + ε)
        ((F.distribution k).input x).graph
        ((F.distribution k).input x).stream at hamp
  have hstrict : 1 - γ < 1 - (1 - target) ^ copies := by linarith
  exact (not_lt_of_ge hx') (hstrict.trans_le hamp)

end SequentialBlueprintHardFamily

end Formal.Streaming
