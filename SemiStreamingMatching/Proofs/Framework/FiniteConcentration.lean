import Mathlib.Tactic

open scoped BigOperators

namespace Formal.Streaming

theorem finite_card_deviation_le_of_sum_sq_le
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (X : Omega → ℚ) (mu a variance pBad : ℚ)
    (ha : 0 < a)
    (hvariance : ∑ omega, (X omega - mu) ^ 2 ≤
      variance * Fintype.card Omega)
    (hprob : variance / a ^ 2 ≤ pBad) :
    (((Finset.univ.filter fun omega ↦
        a ≤ |X omega - mu|).card : ℕ) : ℚ) ≤
      pBad * Fintype.card Omega := by
  let bad := Finset.univ.filter fun omega ↦ a ≤ |X omega - mu|
  have haSq : 0 < a ^ 2 := sq_pos_of_pos ha
  have hpoint : ∀ omega ∈ bad, a ^ 2 ≤ (X omega - mu) ^ 2 := by
    intro omega homega
    have habs : a ≤ |X omega - mu| := (Finset.mem_filter.1 homega).2
    nlinarith [sq_nonneg (X omega - mu), abs_nonneg (X omega - mu),
      sq_abs (X omega - mu)]
  have hsumBad : a ^ 2 * (bad.card : ℚ) ≤
      ∑ omega in bad, (X omega - mu) ^ 2 := by
    calc
      a ^ 2 * (bad.card : ℚ) = ∑ _omega in bad, a ^ 2 := by
        simp [mul_comm]
      _ ≤ ∑ omega in bad, (X omega - mu) ^ 2 := by
        exact Finset.sum_le_sum fun omega homega ↦ hpoint omega homega
  have hsumAll : (∑ omega in bad, (X omega - mu) ^ 2) ≤
      ∑ omega, (X omega - mu) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro _omega _hnot _hall
    positivity
  have hcard : (bad.card : ℚ) ≤
      variance / a ^ 2 * Fintype.card Omega := by
    rw [show variance / a ^ 2 * Fintype.card Omega =
      (variance * Fintype.card Omega) / a ^ 2 by ring]
    apply (le_div_iff haSq).2
    calc
      (bad.card : ℚ) * a ^ 2 = a ^ 2 * (bad.card : ℚ) := by ring
      _ ≤ ∑ omega in bad, (X omega - mu) ^ 2 := hsumBad
      _ ≤ ∑ omega, (X omega - mu) ^ 2 := hsumAll
      _ ≤ variance * Fintype.card Omega := hvariance
  change (bad.card : ℚ) ≤ pBad * Fintype.card Omega
  exact hcard.trans (mul_le_mul_of_nonneg_right hprob (by positivity))

theorem finite_card_upper_tail_le_of_sum_sq_le
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (X : Omega → ℚ) (mu a variance pBad : ℚ)
    (ha : 0 < a)
    (hvariance : ∑ omega, (X omega - mu) ^ 2 ≤
      variance * Fintype.card Omega)
    (hprob : variance / a ^ 2 ≤ pBad) :
    (((Finset.univ.filter fun omega ↦
        mu + a ≤ X omega).card : ℕ) : ℚ) ≤
      pBad * Fintype.card Omega := by
  have hsubset : (Finset.univ.filter fun omega ↦ mu + a ≤ X omega) ⊆
      Finset.univ.filter fun omega ↦ a ≤ |X omega - mu| := by
    intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
    have hnonneg : 0 ≤ X omega - mu := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  have hcard := Finset.card_le_card hsubset
  have hcheb := finite_card_deviation_le_of_sum_sq_le X mu a variance pBad
    ha hvariance hprob
  have hcardQ :
      (((Finset.univ.filter fun omega ↦ mu + a ≤ X omega).card : ℕ) : ℚ) ≤
        ((Finset.univ.filter fun omega ↦ a ≤ |X omega - mu|).card : ℚ) := by
    exact_mod_cast hcard
  exact hcardQ.trans hcheb

end Formal.Streaming
