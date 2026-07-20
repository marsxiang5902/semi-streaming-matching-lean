import SemiStreamingMatching.Proofs.Framework.HardnessCertificate
import SemiStreamingMatching.Proofs.Framework.StreamingReduction
import Mathlib.Tactic

namespace Formal.Streaming

open BipartiteGraph

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

namespace MatchingGapCertificate

variable {G : BipartiteGraph L R}

theorem not_meetsApproximation_of_few_special
    (cert : MatchingGapCertificate G)
    {M : Finset (Edge L R)} {q : ℕ} {ρ : ℚ}
    (hM : G.IsMatching M)
    (hspecial : (M ∩ cert.special).card ≤ q)
    (hρ : 0 ≤ ρ)
    (hgap : ((cert.ordinaryUpper + q : ℕ) : ℚ) <
      ρ * cert.optimumLower) :
    ¬ OnePassAlgorithm.MeetsApproximation ρ G M := by
  intro happrox
  have hcard := cert.matching_card_le hM hspecial
  have hopt : (cert.optimumLower : ℚ) ≤ G.matchingNumber := by
    exact_mod_cast cert.optimumLower_le
  have hmul : ρ * cert.optimumLower ≤ ρ * G.matchingNumber :=
    mul_le_mul_of_nonneg_left hopt hρ
  have hupper : (M.card : ℚ) ≤ cert.ordinaryUpper + q := by
    exact_mod_cast hcard
  have hgap' : (cert.ordinaryUpper : ℚ) + q <
      ρ * cert.optimumLower := by
    simpa only [Nat.cast_add] using hgap
  linarith [happrox.2]

end MatchingGapCertificate

namespace FinitePartitionDistribution

variable {P : ℕ}

noncomputable def successfulSamples
    (D : FinitePartitionDistribution P L R)
    (prot : BlackboardProtocol P L R) (ρ : ℚ) : Finset D.Sample := by
  classical
  exact Finset.univ.filter fun x => prot.SucceedsOn ρ (D.input x)

theorem protocolSuccessMass_eq_card
    (D : FinitePartitionDistribution P L R)
    (prot : BlackboardProtocol P L R) (ρ : ℚ) :
    D.protocolSuccessMass prot ρ =
      ((D.successfulSamples prot ρ).card : ℚ) := by
  classical
  unfold protocolSuccessMass successfulSamples
  rw [Finset.sum_ite]
  simp

def DiscoversManySpecial
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (q : ℕ) (prot : BlackboardProtocol P L R) (x : D.Sample) : Prop :=
  q < (prot.result (D.input x) ∩ (cert x).special).card

noncomputable def manySpecialSamples
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (q : ℕ) (prot : BlackboardProtocol P L R) : Finset D.Sample := by
  classical
  exact Finset.univ.filter fun x => D.DiscoversManySpecial cert q prot x

noncomputable def successfulManySpecialSamples
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (q : ℕ) (ρ : ℚ) (prot : BlackboardProtocol P L R) : Finset D.Sample := by
  classical
  exact Finset.univ.filter fun x =>
    prot.SucceedsOn ρ (D.input x) ∧ D.DiscoversManySpecial cert q prot x

noncomputable def badSamples
    (D : FinitePartitionDistribution P L R) (Good : D.Sample → Prop) :
    Finset D.Sample := by
  classical
  exact Finset.univ.filter fun x => ¬ Good x

theorem isHardForCommunication_of_few_special
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    {q s : ℕ} {ρ p : ℚ}
    (hρ : 0 ≤ ρ)
    (hgap : ∀ x : D.Sample,
      (((cert x).ordinaryUpper + q : ℕ) : ℚ) <
        ρ * (cert x).optimumLower)
    (hdiscovery : ∀ prot : BlackboardProtocol P L R,
      prot.UsesCommunication s →
      ((D.manySpecialSamples cert q prot).card : ℚ) ≤
          p * Fintype.card D.Sample) :
    D.IsHardForCommunication ρ p s := by
  classical
  intro prot hprot
  rw [D.protocolSuccessMass_eq_card prot ρ]
  have hsubset :
      D.successfulSamples prot ρ ⊆
        D.manySpecialSamples cert q prot := by
    intro x hx
    have hsuc : prot.SucceedsOn ρ (D.input x) := by
      simpa [successfulSamples] using hx
    simp only [manySpecialSamples, Finset.mem_filter, Finset.mem_univ,
      true_and]
    by_contra hnot
    have hfew :
        (prot.result (D.input x) ∩ (cert x).special).card ≤ q := by
      exact Nat.le_of_not_gt hnot
    exact (cert x).not_meetsApproximation_of_few_special
      hsuc.1 hfew hρ (hgap x) hsuc
  have hcard := Finset.card_le_card hsubset
  exact le_trans (by exact_mod_cast hcard) (hdiscovery prot hprot)

theorem isHardForCommunication_of_success_many_special
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    {q s : ℕ} {ρ p : ℚ}
    (hρ : 0 ≤ ρ)
    (hgap : ∀ x : D.Sample,
      (((cert x).ordinaryUpper + q : ℕ) : ℚ) <
        ρ * (cert x).optimumLower)
    (hdiscovery : ∀ prot : BlackboardProtocol P L R,
      prot.UsesCommunication s →
      ((D.successfulManySpecialSamples cert q ρ prot).card : ℚ) ≤
            p * Fintype.card D.Sample) :
    D.IsHardForCommunication ρ p s := by
  classical
  intro prot hprot
  rw [D.protocolSuccessMass_eq_card prot ρ]
  have hsubset :
      D.successfulSamples prot ρ ⊆
        D.successfulManySpecialSamples cert q ρ prot := by
    intro x hx
    have hsuc : prot.SucceedsOn ρ (D.input x) := by
      simpa [successfulSamples] using hx
    simp only [successfulManySpecialSamples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨hsuc, ?_⟩
    by_contra hnot
    have hfew :
        (prot.result (D.input x) ∩ (cert x).special).card ≤ q :=
      Nat.le_of_not_gt hnot
    exact (cert x).not_meetsApproximation_of_few_special
      hsuc.1 hfew hρ (hgap x) hsuc
  have hcard := Finset.card_le_card hsubset
  exact le_trans (by exact_mod_cast hcard) (hdiscovery prot hprot)

theorem isHardForCommunication_of_good_success_many_special
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (Good : D.Sample → Prop)
    {q s : ℕ} {ρ pBad pMany : ℚ}
    (hρ : 0 ≤ ρ)
    (hgap : ∀ x : D.Sample, Good x →
      (((cert x).ordinaryUpper + q : ℕ) : ℚ) <
        ρ * (cert x).optimumLower)
    (hbad : ((D.badSamples Good).card : ℚ) ≤
      pBad * Fintype.card D.Sample)
    (hmany : ∀ prot : BlackboardProtocol P L R,
      prot.UsesCommunication s →
      ((D.successfulManySpecialSamples cert q ρ prot).card : ℚ) ≤
        pMany * Fintype.card D.Sample) :
    D.IsHardForCommunication ρ (pBad + pMany) s := by
  classical
  intro prot hprot
  rw [D.protocolSuccessMass_eq_card prot ρ]
  have hsubset :
      D.successfulSamples prot ρ ⊆
        D.badSamples Good ∪
          D.successfulManySpecialSamples cert q ρ prot := by
    intro x hx
    have hsuc : prot.SucceedsOn ρ (D.input x) := by
      simpa [successfulSamples] using hx
    by_cases hxgood : Good x
    · apply Finset.mem_union_right
      simp only [successfulManySpecialSamples, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨hsuc, ?_⟩
      by_contra hnot
      have hfew :
          (prot.result (D.input x) ∩ (cert x).special).card ≤ q :=
        Nat.le_of_not_gt hnot
      exact (cert x).not_meetsApproximation_of_few_special
        hsuc.1 hfew hρ (hgap x hxgood) hsuc
    · apply Finset.mem_union_left
      simp [badSamples, hxgood]
  have hcard :
      (D.successfulSamples prot ρ).card ≤
        (D.badSamples Good).card +
          (D.successfulManySpecialSamples cert q ρ prot).card :=
    le_trans (Finset.card_le_card hsubset)
      (Finset.card_union_le _ _)
  have hcardQ :
      ((D.successfulSamples prot ρ).card : ℚ) ≤
        (D.badSamples Good).card +
          (D.successfulManySpecialSamples cert q ρ prot).card := by
    exact_mod_cast hcard
  calc
    ((D.successfulSamples prot ρ).card : ℚ) ≤
        (D.badSamples Good).card +
          (D.successfulManySpecialSamples cert q ρ prot).card := hcardQ
    _ ≤ pBad * Fintype.card D.Sample +
        pMany * Fintype.card D.Sample := add_le_add hbad (hmany prot hprot)
    _ = (pBad + pMany) * Fintype.card D.Sample := by ring

end FinitePartitionDistribution

end Formal.Streaming
