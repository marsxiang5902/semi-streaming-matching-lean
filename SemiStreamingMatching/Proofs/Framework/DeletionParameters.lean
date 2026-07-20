import SemiStreamingMatching.Proofs.Framework.DeletionExpectation
import Mathlib.Tactic

open scoped BigOperators

namespace Formal.Streaming

theorem finite_badSet_card_le_of_sum_le
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (bad : Finset Omega) (X : Omega -> Nat) {d : Nat} (hd : 0 < d)
    (hbad : forall omega, omega ∈ bad -> d < X omega) {mu p : Rat}
    (hmean : (∑ omega, (X omega : Rat)) <= mu * Fintype.card Omega)
    (hprob : mu / d <= p) :
    (bad.card : Rat) <= p * Fintype.card Omega := by
  have hmarkovNat : d * bad.card <= ∑ omega, X omega := by
    calc
      d * bad.card = ∑ _omega in bad, d := by
        simp [Nat.mul_comm]
      _ <= ∑ omega in bad, X omega := by
        apply Finset.sum_le_sum
        intro omega homega
        exact Nat.le_of_lt (hbad omega homega)
      _ <= ∑ omega, X omega :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
          (fun _ _ _ => Nat.zero_le _)
  have hmarkov :
      (d : Rat) * bad.card <= ∑ omega, (X omega : Rat) := by
    exact_mod_cast hmarkovNat
  have hdRat : (0 : Rat) < d := by
    exact_mod_cast hd
  have hcard :
      (bad.card : Rat) <= mu / d * Fintype.card Omega := by
    rw [show mu / (d : Rat) * Fintype.card Omega =
      (mu * Fintype.card Omega) / d by ring]
    apply (le_div_iff hdRat).2
    calc
      (bad.card : Rat) * d = d * bad.card := by ring
      _ <= ∑ omega, (X omega : Rat) := hmarkov
      _ <= mu * Fintype.card Omega := hmean
  exact hcard.trans
    (mul_le_mul_of_nonneg_right hprob (by positivity))

namespace HardDistribution

open SimpleExpansion

variable {L R : Type*} {r t : Nat}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def playerPartSize (B : SimpleProperBlueprint) (r t : Nat)
    (p : Fin B.P) : Nat :=
  Fintype.card (SuffixIndexTuple B t p) * ((B.E p).card * r ^ B.P)

theorem playerPartSize_eq_part_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) :
    playerPartSize B r t p = (part B H J p).card := by
  rw [part_card]
  rfl

def floorDeletionCount (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) : Nat :=
  numerator * playerPartSize B r t p / denominator

theorem denominator_mul_floorDeletionCount_le
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) :
    denominator * floorDeletionCount B r t numerator denominator p <=
      numerator * playerPartSize B r t p := by
  simpa only [floorDeletionCount, Nat.mul_comm] using
    Nat.div_mul_le_self (numerator * playerPartSize B r t p) denominator

theorem numerator_mul_partSize_lt_denominator_mul_floorDeletionCount_add_one
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hdenominator : 0 < denominator) :
    numerator * playerPartSize B r t p <
      denominator * (floorDeletionCount B r t numerator denominator p + 1) := by
  simpa only [floorDeletionCount] using
    Nat.lt_mul_div_succ
      (numerator * playerPartSize B r t p) hdenominator

theorem floorDeletionCount_le_playerPartSize
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hnumerator : numerator <= denominator) :
    floorDeletionCount B r t numerator denominator p <=
      playerPartSize B r t p := by
  unfold floorDeletionCount
  apply Nat.div_le_of_le_mul'
  exact Nat.mul_le_mul_right (playerPartSize B r t p) hnumerator

theorem floorDeletionCount_admissible
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (numerator denominator : Nat) (hnumerator : numerator <= denominator) :
    forall J p,
      floorDeletionCount B r t numerator denominator p <=
        (part B H J p).card := by
  intro J p
  rw [← playerPartSize_eq_part_card B H J p]
  exact floorDeletionCount_le_playerPartSize
    B r t numerator denominator p hnumerator

theorem floorDeletionCount_cast_le_rate_mul_playerPartSize
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hdenominator : 0 < denominator) :
    (floorDeletionCount B r t numerator denominator p : Rat) <=
      ((numerator : Rat) / denominator) * playerPartSize B r t p := by
  have hdenominatorRat : (0 : Rat) < denominator := by
    exact_mod_cast hdenominator
  rw [show ((numerator : Rat) / denominator) *
      playerPartSize B r t p =
      ((numerator : Rat) * playerPartSize B r t p) / denominator by ring]
  apply (le_div_iff hdenominatorRat).2
  have hcross := denominator_mul_floorDeletionCount_le
    B r t numerator denominator p
  exact_mod_cast (by simpa only [Nat.mul_comm] using hcross)

theorem floorDeletionCount_cast_le_rate_mul_part_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (numerator denominator : Nat) (J : IndexTuple B t) (p : Fin B.P)
    (hdenominator : 0 < denominator) :
    (floorDeletionCount B r t numerator denominator p : Rat) <=
      ((numerator : Rat) / denominator) * (part B H J p).card := by
  rw [← playerPartSize_eq_part_card B H J p]
  exact floorDeletionCount_cast_le_rate_mul_playerPartSize
    B r t numerator denominator p hdenominator

theorem floorDeletionCount_pos
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hdenominator : 0 < denominator)
    (hlarge : denominator <= numerator * playerPartSize B r t p) :
    0 < floorDeletionCount B r t numerator denominator p := by
  simpa only [floorDeletionCount] using
    (Nat.one_le_div_iff hdenominator).2 hlarge

theorem rate_sub_one_div_playerPartSize_lt_floorDeletionRate
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hdenominator : 0 < denominator)
    (hpart : 0 < playerPartSize B r t p) :
    (numerator : Rat) / denominator -
        1 / playerPartSize B r t p <
      (floorDeletionCount B r t numerator denominator p : Rat) /
        playerPartSize B r t p := by
  have hdenominatorRat : (0 : Rat) < denominator := by
    exact_mod_cast hdenominator
  have hpartRat : (0 : Rat) < playerPartSize B r t p := by
    exact_mod_cast hpart
  apply (sub_lt_iff_lt_add).2
  rw [show
    (floorDeletionCount B r t numerator denominator p : Rat) /
          playerPartSize B r t p + 1 / playerPartSize B r t p =
        ((floorDeletionCount B r t numerator denominator p : Rat) + 1) /
          playerPartSize B r t p by ring]
  apply (div_lt_div_iff hdenominatorRat hpartRat).2
  have hcross :=
    numerator_mul_partSize_lt_denominator_mul_floorDeletionCount_add_one
      B r t numerator denominator p hdenominator
  exact_mod_cast (by simpa only [Nat.mul_comm] using hcross)

theorem targetRate_lt_floorDeletionRate_of_large
    (B : SimpleProperBlueprint) (r t numerator denominator : Nat)
    (p : Fin B.P) (hdenominator : 0 < denominator)
    (hpart : 0 < playerPartSize B r t p) (target : Rat)
    (hlarge : target + 1 / playerPartSize B r t p <=
      (numerator : Rat) / denominator) :
    target <
      (floorDeletionCount B r t numerator denominator p : Rat) /
        playerPartSize B r t p := by
  have hlower := rate_sub_one_div_playerPartSize_lt_floorDeletionRate
    B r t numerator denominator p hdenominator hpart
  linarith

@[simp]
theorem mem_canonicalDeletionBadSamples_iff
    {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P -> Nat} (d : Nat) (sample : Sample B H q) :
    sample ∈ canonicalDeletionBadSamples (B := B) (H := H) (q := q) d <->
      d < canonicalDeletionCount sample := by
  classical
  simp [canonicalDeletionBadSamples]

set_option maxHeartbeats 1200000 in

theorem canonicalDeletionBadBound_of_mean
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P -> Nat) {d : Nat} (hd : 0 < d) {mu pBad : Rat}
    (hmean :
      (∑ sample : Sample B H q, (canonicalDeletionCount sample : Rat)) <=
        mu * Fintype.card (Sample B H q))
    (hprob : mu / d <= pBad) :
    CanonicalDeletionBadBound B H q d pBad := by
  classical
  let Omega := Sample B H q
  let bad : Finset Omega :=
    canonicalDeletionBadSamples (B := B) (H := H) (q := q) d
  let X : Omega -> Nat := fun sample => canonicalDeletionCount sample
  refine { card_le := ?_ }
  change (bad.card : Rat) <= pBad * Fintype.card Omega
  apply finite_badSet_card_le_of_sum_le bad X hd
  · intro sample hsample
    apply (mem_canonicalDeletionBadSamples_iff
      (B := B) (H := H) (q := q) d sample).1
    exact hsample
  · exact hmean
  · exact hprob

set_option maxHeartbeats 1200000 in

theorem canonicalDeletionBadBound_of_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P -> Nat)
    (hq : forall J p, q p <= (part B H J p).card)
    {delta : Rat}
    (hrate : forall J p, (q p : Rat) <= delta * (part B H J p).card)
    {d : Nat} (hd : 0 < d) {pBad : Rat}
    (hprob :
      (delta * (B.edgeCount * r ^ B.P)) / d <= pBad) :
    CanonicalDeletionBadBound B H q d pBad := by
  refine canonicalDeletionBadBound_of_mean B H q hd
    (mu := delta * (B.edgeCount * r ^ B.P)) ?_ hprob
  exact canonicalDeletionCount_sum_le B H q hq hrate

set_option maxHeartbeats 1200000 in

theorem canonicalDeletionBadBound_of_div_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P -> Nat)
    (hq : forall J p, q p <= (part B H J p).card)
    (hpart : forall J p, 0 < (part B H J p).card)
    {delta : Rat}
    (hrate : forall J p,
      (q p : Rat) / (part B H J p).card <= delta)
    {d : Nat} (hd : 0 < d) {pBad : Rat}
    (hprob :
      (delta * (B.edgeCount * r ^ B.P)) / d <= pBad) :
    CanonicalDeletionBadBound B H q d pBad := by
  refine canonicalDeletionBadBound_of_mean B H q hd
    (mu := delta * (B.edgeCount * r ^ B.P)) ?_ hprob
  exact canonicalDeletionCount_sum_le_of_div_rate B H q hq hpart hrate

set_option maxHeartbeats 1200000 in

theorem floorDeletionCount_canonicalDeletionBadBound
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hnumerator : numerator <= denominator)
    {d : Nat} (hd : 0 < d) {pBad : Rat}
    (hprob :
      ((((numerator : Rat) / denominator) *
          (B.edgeCount * r ^ B.P)) / d) <= pBad) :
    CanonicalDeletionBadBound B H
      (floorDeletionCount B r t numerator denominator) d pBad := by
  apply canonicalDeletionBadBound_of_rate B H
    (floorDeletionCount B r t numerator denominator)
    (floorDeletionCount_admissible B H numerator denominator hnumerator)
    (delta := (numerator : Rat) / denominator) (d := d) (pBad := pBad)
  intro J p
  exact floorDeletionCount_cast_le_rate_mul_part_card
    B H numerator denominator J p hdenominator
  · exact hd
  · exact hprob

end HardDistribution

end Formal.Streaming
