import SemiStreamingMatching.Definitions.Asymptotics
import SemiStreamingMatching.Proofs.Framework.ERS
import SemiStreamingMatching.Proofs.Framework.Expansion
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

structure ERSSequence (C : ℕ) where
  n : ℕ → ℕ
  r : ℕ → ℕ
  t : ℕ → ℕ
  host : (k : ℕ) → ERSGraph (Fin (n k)) (Fin (n k)) C (r k) (t k)

namespace ERSSequence

variable {C : ℕ}

@[simp]
theorem left_card (F : ERSSequence C) (k : ℕ) :
    Fintype.card (Fin (F.n k)) = F.n k := by simp

@[simp]
theorem right_card (F : ERSSequence C) (k : ℕ) :
    Fintype.card (Fin (F.n k)) = F.n k := by simp

def augmentedExpansionSize (F : ERSSequence C) (P k : ℕ) : ℕ :=
  2 * (F.n k) ^ P

end ERSSequence

structure DenseERSSequence (C : ℕ) extends ERSSequence C where
  relativeLossNumerator : ℕ
  relativeLossDenominator : ℕ
  relativeLoss_lt : relativeLossNumerator < relativeLossDenominator
  matching_dense : ∀ k,
    (relativeLossDenominator - relativeLossNumerator) * n k ≤
      relativeLossDenominator * (C * r k)
  baseSizesGrow : SizesTendToInfinity n
  multiplicityGrowth : ∀ P, 0 < P →
    DominatesPolylogAlong
      (ERSSequence.augmentedExpansionSize toERSSequence P) t

namespace DenseERSSequence

variable {C : ℕ}

theorem augmentedSizesTendToInfinity (F : DenseERSSequence C)
    {P : ℕ} (hP : 0 < P) :
    SizesTendToInfinity (F.augmentedExpansionSize P) := by
  intro N
  obtain ⟨k₀, hk₀⟩ := F.baseSizesGrow (max N 1)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hnmax := hk₀ k hk
  have hN : N ≤ F.n k := le_trans (le_max_left _ _) hnmax
  have hnpos : 0 < F.n k := lt_of_lt_of_le (by omega) hnmax
  have hpow : F.n k ≤ (F.n k) ^ P := by
    simpa using Nat.pow_le_pow_right hnpos (show 1 ≤ P by omega)
  calc
    N ≤ F.n k := hN
    _ ≤ (F.n k) ^ P := hpow
    _ ≤ F.augmentedExpansionSize P k := by
      simp only [ERSSequence.augmentedExpansionSize]
      omega

theorem semiStreaming_space_domination (B : SimpleProperBlueprint)
    (F : DenseERSSequence B.C) {space : ℕ → ℕ}
    (hspace : IsSemiStreamingSpace space) (q : ℕ) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      q * space (F.augmentedExpansionSize B.P k) ≤
        F.augmentedExpansionSize B.P k * F.t k := by
  exact semiStreaming_along_eventually_le_size_mul hspace
    (F.augmentedSizesTendToInfinity B.hP)
    (F.multiplicityGrowth B.P B.hP) q

end DenseERSSequence

def allMatchingEdgesOf {n C t : ℕ}
    (M : Fin t → Fin C → Fin C →
      Finset (Formal.Streaming.Edge (Fin n) (Fin n))) :
    Finset (Formal.Streaming.Edge (Fin n) (Fin n)) :=
  Finset.univ.biUnion fun i ↦ ERSGraph.matchingGroupOf M i

@[simp]
theorem mem_allMatchingEdgesOf_iff {n C t : ℕ}
    (M : Fin t → Fin C → Fin C →
      Finset (Formal.Streaming.Edge (Fin n) (Fin n)))
    (e : Formal.Streaming.Edge (Fin n) (Fin n)) :
    e ∈ allMatchingEdgesOf M ↔
      ∃ i x y, e ∈ M i x y := by
  simp [allMatchingEdgesOf, ERSGraph.matchingGroupOf]

structure AppendixBFiniteData (C : ℕ) where
  n : ℕ
  r : ℕ
  t : ℕ
  d : ℕ
  supportWeight : ℕ
  intersectionCap : ℕ
  C_pos : 0 < C
  r_pos : 0 < r
  t_pos : 0 < t
  supports : Fin t → Finset (Fin d)
  support_card : ∀ i, (supports i).card = supportWeight
  intersection_lt_support : intersectionCap < supportWeight
  support_intersection : ∀ {i j}, i ≠ j →
    ((supports i) ∩ (supports j)).card ≤ intersectionCap
  matching : Fin t → Fin C → Fin C →
    Finset (Formal.Streaming.Edge (Fin n) (Fin n))
  leftGroup : Fin t → Fin C → Finset (Fin n)
  rightGroup : Fin t → Fin C → Finset (Fin n)
  matching_card : ∀ i x y, (matching i x y).card = r
  matching_left_unique :
    ∀ {i x y} {e f : Formal.Streaming.Edge (Fin n) (Fin n)},
      e ∈ matching i x y → f ∈ matching i x y → e.1 = f.1 → e = f
  matching_right_unique :
    ∀ {i x y} {e f : Formal.Streaming.Edge (Fin n) (Fin n)},
      e ∈ matching i x y → f ∈ matching i x y → e.2 = f.2 → e = f
  matching_between :
    ∀ {i x y} {e : Formal.Streaming.Edge (Fin n) (Fin n)},
      e ∈ matching i x y → e.1 ∈ leftGroup i x ∧ e.2 ∈ rightGroup i y
  left_groups_disjoint :
    ∀ i {x y}, x ≠ y → Disjoint (leftGroup i x) (leftGroup i y)
  right_groups_disjoint :
    ∀ i {x y}, x ≠ y → Disjoint (rightGroup i x) (rightGroup i y)
  left_decomposition : ∀ i,
    ERSGraph.leftVertices (ERSGraph.matchingGroupOf matching i) =
      ERSGraph.vertexGroupUnion (leftGroup i)
  right_decomposition : ∀ i,
    ERSGraph.rightVertices (ERSGraph.matchingGroupOf matching i) =
      ERSGraph.vertexGroupUnion (rightGroup i)
  matching_groups_disjoint :
    ∀ {i j}, i ≠ j →
      Disjoint (ERSGraph.matchingGroupOf matching i)
        (ERSGraph.matchingGroupOf matching j)
  cross_induced :
    ∀ {i j}, i ≠ j →
      ∀ {e : Formal.Streaming.Edge (Fin n) (Fin n)},
        e ∈ ERSGraph.matchingGroupOf matching j →
        e.1 ∈ ERSGraph.leftVertices (ERSGraph.matchingGroupOf matching i) →
        e.2 ∈ ERSGraph.rightVertices (ERSGraph.matchingGroupOf matching i) →
        ∃ x, e.1 ∈ leftGroup i x ∧ e.2 ∈ rightGroup i x

namespace AppendixBFiniteData

variable {C : ℕ}

theorem supports_injective (D : AppendixBFiniteData C) :
    Function.Injective D.supports := by
  intro i j hij
  by_contra hne
  have hinter := D.support_intersection hne
  have heq : (D.supports i ∩ D.supports j).card = D.supportWeight := by
    rw [hij, Finset.inter_self, D.support_card]
  have hle : D.supportWeight ≤ D.intersectionCap := heq ▸ hinter
  exact (not_le_of_gt D.intersection_lt_support) hle

def graph (D : AppendixBFiniteData C) : BipartiteGraph (Fin D.n) (Fin D.n) where
  edges := allMatchingEdgesOf D.matching

def toERSGraph (D : AppendixBFiniteData C) :
    ERSGraph (Fin D.n) (Fin D.n) C D.r D.t where
  graph := D.graph
  matching := D.matching
  leftGroup := D.leftGroup
  rightGroup := D.rightGroup
  C_pos := D.C_pos
  r_pos := D.r_pos
  t_pos := D.t_pos
  side_card_eq := by simp
  matching_isMatching := by
    intro i x y
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      change e ∈ allMatchingEdgesOf D.matching
      rw [mem_allMatchingEdgesOf_iff]
      exact ⟨i, x, y, he⟩
    · intro e f he hf hef
      exact D.matching_left_unique he hf hef
    · intro e f he hf hef
      exact D.matching_right_unique he hf hef
  matching_card := D.matching_card
  matching_groups_disjoint := D.matching_groups_disjoint
  left_groups_disjoint := D.left_groups_disjoint
  right_groups_disjoint := D.right_groups_disjoint
  matching_between := D.matching_between
  left_decomposition := D.left_decomposition
  right_decomposition := D.right_decomposition
  inducedness := by
    intro i e he hnot hl hr
    change e ∈ allMatchingEdgesOf D.matching at he
    rw [mem_allMatchingEdgesOf_iff] at he
    obtain ⟨j, x, y, hej⟩ := he
    have hejGroup : e ∈ ERSGraph.matchingGroupOf D.matching j := by
      rw [ERSGraph.matchingGroupOf]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨x, y, hej⟩
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hnot hejGroup
    exact D.cross_induced (i := i) (j := j) hji.symm hejGroup hl hr

end AppendixBFiniteData

structure AppendixBSequenceData (C : ℕ) where
  finite : ℕ → AppendixBFiniteData C
  relativeLossNumerator : ℕ
  relativeLossDenominator : ℕ
  relativeLoss_lt : relativeLossNumerator < relativeLossDenominator
  matching_dense : ∀ k,
    (relativeLossDenominator - relativeLossNumerator) * (finite k).n ≤
      relativeLossDenominator * (C * (finite k).r)
  baseSizesGrow : SizesTendToInfinity fun k ↦ (finite k).n
  multiplicityGrowth : ∀ P, 0 < P →
    DominatesPolylogAlong
      (fun k ↦ 2 * ((finite k).n) ^ P)
      (fun k ↦ (finite k).t)

namespace AppendixBSequenceData

variable {C : ℕ}

def toDenseERSSequence (D : AppendixBSequenceData C) : DenseERSSequence C where
  toERSSequence :=
    { n := fun k ↦ (D.finite k).n
      r := fun k ↦ (D.finite k).r
      t := fun k ↦ (D.finite k).t
      host := fun k ↦ (D.finite k).toERSGraph }
  relativeLossNumerator := D.relativeLossNumerator
  relativeLossDenominator := D.relativeLossDenominator
  relativeLoss_lt := D.relativeLoss_lt
  matching_dense := D.matching_dense
  baseSizesGrow := D.baseSizesGrow
  multiplicityGrowth := by
    intro P hP
    simpa [ERSSequence.augmentedExpansionSize] using D.multiplicityGrowth P hP

@[simp]
theorem toDenseERSSequence_n (D : AppendixBSequenceData C) (k : ℕ) :
    D.toDenseERSSequence.n k = (D.finite k).n := rfl

@[simp]
theorem toDenseERSSequence_r (D : AppendixBSequenceData C) (k : ℕ) :
    D.toDenseERSSequence.r k = (D.finite k).r := rfl

@[simp]
theorem toDenseERSSequence_t (D : AppendixBSequenceData C) (k : ℕ) :
    D.toDenseERSSequence.t k = (D.finite k).t := rfl

end AppendixBSequenceData

end ERSFamily

end Formal.Streaming
