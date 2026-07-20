import SemiStreamingMatching.Proofs.Framework.GapArithmetic
import SemiStreamingMatching.Proofs.Framework.HardDistribution
import SemiStreamingMatching.Proofs.Framework.SpecialEdgeLowerBound
import Mathlib.Tactic

namespace Formal.Streaming

open scoped BigOperators

theorem threshold_mul_card_lt_le_sum
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (X : Ω → ℕ) (d : ℕ) :
    d * (Finset.univ.filter fun ω => d < X ω).card ≤ ∑ ω, X ω := by
  calc
    d * (Finset.univ.filter fun ω => d < X ω).card =
        ∑ _ω in Finset.univ.filter (fun ω => d < X ω), d := by
      simp [Nat.mul_comm]
    _ ≤ ∑ ω in Finset.univ.filter (fun ω => d < X ω), X ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact Nat.le_of_lt (Finset.mem_filter.1 hω).2
    _ ≤ ∑ ω, X ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

theorem card_threshold_lt_le_of_sum_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (X : Ω → ℕ) {d : ℕ} (hd : 0 < d) {μ p : ℚ}
    (hmean : (∑ ω, (X ω : ℚ)) ≤ μ * Fintype.card Ω)
    (hp : μ / d ≤ p) :
    ((Finset.univ.filter fun ω => d < X ω).card : ℚ) ≤
      p * Fintype.card Ω := by
  have hmarkovNat := threshold_mul_card_lt_le_sum X d
  have hmarkov :
      (d : ℚ) * (Finset.univ.filter fun ω => d < X ω).card ≤
        ∑ ω, (X ω : ℚ) := by
    exact_mod_cast hmarkovNat
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hcard :
      ((Finset.univ.filter fun ω => d < X ω).card : ℚ) ≤
        μ / d * Fintype.card Ω := by
    rw [show μ / (d : ℚ) * Fintype.card Ω =
      (μ * Fintype.card Ω) / d by ring]
    apply (le_div_iff hdQ).2
    calc
      ((Finset.univ.filter fun ω => d < X ω).card : ℚ) * d =
          d * (Finset.univ.filter fun ω => d < X ω).card := by ring
      _ ≤ ∑ ω, (X ω : ℚ) := hmarkov
      _ ≤ μ * Fintype.card Ω := hmean
  exact hcard.trans (mul_le_mul_of_nonneg_right hp (by positivity))

namespace HardDistribution

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def canonicalDeletionCount {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ}
    (s : Sample B H q) : ℕ :=
  (canonicalMatching B H s.1 \ keptEdges s).card

def CanonicalDeletionGood {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ}
    (d : ℕ) (s : Sample B H q) : Prop :=
  canonicalDeletionCount s ≤ d

@[simp]
theorem not_canonicalDeletionGood_iff {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ}
    (d : ℕ) (s : Sample B H q) :
    ¬ CanonicalDeletionGood d s ↔ d < canonicalDeletionCount s := by
  simp [CanonicalDeletionGood]

noncomputable def canonicalDeletionBadSamples {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (d : ℕ) :
    Finset (Sample B H q) := by
  classical
  exact Finset.univ.filter fun s => ¬ CanonicalDeletionGood d s

theorem exactSampleCertificate_gap_of_good
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    {qDelete : Fin B.P → ℕ} (s : Sample B H qDelete)
    {d qSpecial : ℕ} (hgood : CanonicalDeletionGood d s)
    {a eta epsilon : ℚ}
    (hmd : B.edgeCount * r ^ B.P + d ≤
      2 * (Fintype.card L) ^ B.P)
    (ha0 : 0 ≤ a) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hxLower : blueprintValueRat B - a ≤
      ((B.edgeCount * r ^ B.P : ℕ) : ℚ) /
        ((Fintype.card L) ^ B.P : ℕ))
    (hxUpper : ((B.edgeCount * r ^ B.P : ℕ) : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ blueprintValueRat B + a)
    (hNumeratorError : 2 * a + (qSpecial : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ eta)
    (hDenominatorError : a + (d : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ eta)
    (hSlack : 8 * eta < epsilon) :
    (((exactSampleCertificate s).ordinaryUpper + qSpecial : ℕ) : ℚ) <
      (blueprintRatioRat B + epsilon) *
        (exactSampleCertificate s).optimumLower := by
  have hactual : canonicalDeletionCount s ≤ d := hgood
  have hmdActual : B.edgeCount * r ^ B.P + canonicalDeletionCount s ≤
      2 * (Fintype.card L) ^ B.P := by omega
  have hdenActual : a + (canonicalDeletionCount s : ℚ) /
      ((Fintype.card L) ^ B.P : ℕ) ≤ eta := by
    have hN : (0 : ℚ) < ((Fintype.card L) ^ B.P : ℕ) := by
      exact_mod_cast Nat.pow_pos (H.left_card_pos)
    have hdiv : (canonicalDeletionCount s : ℚ) /
        ((Fintype.card L) ^ B.P : ℕ) ≤
      (d : ℚ) / ((Fintype.card L) ^ B.P : ℕ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hactual) hN.le
    linarith
  have hbase := AugmentedExpansion.expansion_matchingGapCertificate_gap
    (B := B) H s.1 (kept := keptEdges s)
    (d := canonicalDeletionCount s) (q := qSpecial) (le_refl _)
    hmdActual ha0 heta0 heta1 hxLower hxUpper hNumeratorError
    hdenActual hSlack
  simpa only [exactSampleCertificate, canonicalDeletionCount] using hbase

end HardDistribution

end Formal.Streaming
