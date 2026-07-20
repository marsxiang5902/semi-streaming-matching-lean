import SemiStreamingMatching.Proofs.Framework.Augmentation
import SemiStreamingMatching.Proofs.Framework.FiniteProbability

namespace Formal.Streaming

namespace SpecialEdges

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def uniformSuffixDistribution (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) :
    FiniteDist (SuffixIndexTuple B t p) := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (SuffixIndexTuple B t p) := inferInstance
  exact FiniteDist.uniform (SuffixIndexTuple B t p)

@[simp]
theorem uniformSuffixDistribution_mass (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P)
    (S : SuffixIndexTuple B t p) :
    (uniformSuffixDistribution B H p).mass S =
      1 / Fintype.card (SuffixIndexTuple B t p) := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (SuffixIndexTuple B t p) := inferInstance
  simp [uniformSuffixDistribution]

theorem special_suffix_count_bound (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (SimpleExpansion.Left B L)
      (SimpleExpansion.Right B R))
    (hz : z ∈ edgesAt B H p K) :
    (survivingSuffixes B H p K z).card * t ≤
      B.P * Fintype.card (SuffixIndexTuple B t p) :=
  survivingSuffixes_card_mul_le B H p K z hz

noncomputable def SuffixMakesSpecial (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (SimpleExpansion.Left B L)
      (SimpleExpansion.Right B R)) (S : SuffixIndexTuple B t p) : Prop :=
  S ∈ survivingSuffixes B H p K z

noncomputable instance suffixMakesSpecial_decidable (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (SimpleExpansion.Left B L)
      (SimpleExpansion.Right B R)) :
    DecidablePred (SuffixMakesSpecial B H p K z) := by
  intro S
  unfold SuffixMakesSpecial
  infer_instance

@[simp]
theorem suffixMakesSpecial_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (SimpleExpansion.Left B L)
      (SimpleExpansion.Right B R)) (S : SuffixIndexTuple B t p) :
    SuffixMakesSpecial B H p K z S ↔
      IsSpecial B H (completeWithSuffix p K S) z := by
  classical
  exact mem_survivingSuffixes_iff B H p K z S

theorem uniform_suffix_special_prob_le (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (SimpleExpansion.Left B L)
      (SimpleExpansion.Right B R))
    (hz : z ∈ edgesAt B H p K) :
    (uniformSuffixDistribution B H p).prob
        (SuffixMakesSpecial B H p K z) ≤
      (B.P : ℝ) / t := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (SuffixIndexTuple B t p) := inferInstance
  have hset : (Finset.univ.filter (SuffixMakesSpecial B H p K z)) =
      survivingSuffixes B H p K z := by
    ext S
    simp [SuffixMakesSpecial]
  change (FiniteDist.uniform (SuffixIndexTuple B t p)).prob
      (SuffixMakesSpecial B H p K z) ≤ (B.P : ℝ) / t
  rw [FiniteDist.uniform_prob, hset]
  have hcountNat := special_suffix_count_bound B H p K z hz
  have hcount :
      ((survivingSuffixes B H p K z).card : ℝ) * (t : ℝ) ≤
        (B.P : ℝ) * Fintype.card (SuffixIndexTuple B t p) := by
    exact_mod_cast hcountNat
  have ht : (0 : ℝ) < t := by exact_mod_cast H.t_pos
  have hsuffix : (0 : ℝ) < Fintype.card (SuffixIndexTuple B t p) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card (SuffixIndexTuple B t p))
  exact (div_le_div_iff hsuffix ht).2 hcount

end SpecialEdges

end Formal.Streaming
