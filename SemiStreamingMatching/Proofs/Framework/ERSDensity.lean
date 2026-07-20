import SemiStreamingMatching.Proofs.Framework.ERSFamily
import SemiStreamingMatching.Proofs.Framework.GapArithmetic
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSGraph

variable {L R : Type*} {C r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem matching_density_le_card (H : ERSGraph L R C r t) :
    C * r ≤ Fintype.card L := by
  let i : Fin t := ⟨0, H.t_pos⟩
  let y : Fin C := ⟨0, H.C_pos⟩
  let A := Sigma fun x : Fin C =>
    {l : L // l ∈ BipartiteGraph.leftEndpoints (H.matching i x y)}
  let f : A → L := fun z => z.2.1
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨x, l, hl⟩
    rcases b with ⟨x', l', hl'⟩
    dsimp only [f] at hab
    have hgroup (z : Fin C) (v : L)
        (hv : v ∈ BipartiteGraph.leftEndpoints (H.matching i z y)) :
        v ∈ H.leftGroup i z := by
      rw [BipartiteGraph.mem_leftEndpoints_iff] at hv
      obtain ⟨w, hw⟩ := hv
      exact (H.matching_between hw).1
    have hxx : x = x' := H.left_group_index_unique
      (hgroup x l hl) (by simpa [hab] using hgroup x' l' hl')
    subst x'
    have hll : l = l' := hab
    subst l'
    rfl
  have hcard : Fintype.card A ≤ Fintype.card L :=
    Fintype.card_le_of_injective f hf
  have hA : Fintype.card A = C * r := by
    classical
    dsimp only [A]
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_coe,
      BipartiteGraph.leftEndpoints_card_of_isMatching
        (H.matching_isMatching i _ y), H.matching_card]
    simp
  rwa [hA] at hcard

theorem relative_matching_density_le_one (H : ERSGraph L R C r t) :
    ((r : ℚ) * C) / Fintype.card L ≤ 1 := by
  have hL : (0 : ℚ) < Fintype.card L := by
    exact_mod_cast H.left_card_pos
  apply (div_le_one hL).2
  exact_mod_cast (by
    simpa [Nat.mul_comm] using H.matching_density_le_card)

theorem relative_matching_density_nonneg (_H : ERSGraph L R C r t) :
    0 ≤ ((r : ℚ) * C) / Fintype.card L := by
  positivity

end ERSGraph

namespace ERSFamily

namespace DenseERSSequence

variable {C : ℕ}

noncomputable def loss (F : DenseERSSequence C) : ℚ :=
  F.relativeLossNumerator / F.relativeLossDenominator

theorem loss_nonneg (F : DenseERSSequence C) : 0 ≤ F.loss := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem loss_lt_one (F : DenseERSSequence C) : F.loss < 1 := by
  unfold loss
  apply (div_lt_one (by exact_mod_cast
    (Nat.zero_lt_of_lt F.relativeLoss_lt))).2
  exact_mod_cast F.relativeLoss_lt

theorem one_sub_loss_nonneg (F : DenseERSSequence C) :
    0 ≤ 1 - F.loss := by
  linarith [F.loss_lt_one]

theorem one_sub_loss_le_relative_density (F : DenseERSSequence C) (k : ℕ) :
    1 - F.loss ≤ ((F.r k : ℚ) * C) / F.n k := by
  have hn : 0 < F.n k := by
    simpa using (F.host k).left_card_pos
  have hD : 0 < F.relativeLossDenominator :=
    Nat.zero_lt_of_lt F.relativeLoss_lt
  have hle := F.matching_dense k
  have hleQ :
      (((F.relativeLossDenominator - F.relativeLossNumerator) * F.n k : ℕ) : ℚ) ≤
        ((F.relativeLossDenominator * (C * F.r k) : ℕ) : ℚ) := by
    exact_mod_cast hle
  rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt F.relativeLoss_lt),
    Nat.cast_mul, Nat.cast_mul] at hleQ
  unfold loss
  have hnQ : (0 : ℚ) < F.n k := by exact_mod_cast hn
  have hDQ : (0 : ℚ) < F.relativeLossDenominator := by exact_mod_cast hD
  have hrewrite :
      1 - (F.relativeLossNumerator : ℚ) / F.relativeLossDenominator =
        (F.relativeLossDenominator - F.relativeLossNumerator) /
          F.relativeLossDenominator := by
    field_simp
  rw [hrewrite]
  apply (div_le_div_iff hDQ hnQ).2
  nlinarith

theorem relative_density_le_one (F : DenseERSSequence C) (k : ℕ) :
    ((F.r k : ℚ) * C) / F.n k ≤ 1 := by
  simpa using (F.host k).relative_matching_density_le_one

theorem one_sub_nat_mul_le_pow_one_sub {x : ℚ} (hx1 : x ≤ 1)
    (P : ℕ) :
    1 - P * x ≤ (1 - x) ^ P := by
  have h := one_add_mul_le_pow (a := -x) (by linarith) P
  simpa [sub_eq_add_neg, mul_neg, Nat.cast_ofNat] using h

theorem mul_pow_close
    {v x ell : ℚ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hxLower : 1 - ell ≤ x) (hxUpper : x ≤ 1) (P : ℕ) :
    v - P * ell ≤ v * x ^ P ∧ v * x ^ P ≤ v + P * ell := by
  have hbase0 : 0 ≤ 1 - ell := sub_nonneg.mpr hell1
  have hx0 : 0 ≤ x := le_trans hbase0 hxLower
  have hpowLower : (1 - ell) ^ P ≤ x ^ P := by
    exact pow_le_pow_left hbase0 hxLower P
  have hBernoulli := one_sub_nat_mul_le_pow_one_sub hell1 P
  have hpow1 : x ^ P ≤ 1 := by
    simpa using pow_le_one P hx0 hxUpper
  constructor
  · have hscale : v * (1 - P * ell) ≤ v * x ^ P :=
      mul_le_mul_of_nonneg_left (le_trans hBernoulli hpowLower) hv0
    have hcoeff : v - P * ell ≤ v * (1 - P * ell) := by
      have hPell : 0 ≤ (P : ℚ) * ell := mul_nonneg (Nat.cast_nonneg _) hell0
      nlinarith [mul_le_mul_of_nonneg_right hv1 hPell]
    exact hcoeff.trans hscale
  · have : v * x ^ P ≤ v := by
      simpa using mul_le_mul_of_nonneg_left hpow1 hv0
    have hPell : 0 ≤ (P : ℚ) * ell := mul_nonneg (Nat.cast_nonneg _) hell0
    linarith

theorem canonical_density_bounds (B : SimpleProperBlueprint)
    (F : DenseERSSequence B.C) (k : ℕ)
    (J : SimpleExpansion.IndexTuple B (F.t k)) :
    blueprintValueRat B - B.P * F.loss ≤
        ((SimpleExpansion.canonicalMatching B (F.host k) J).card : ℚ) /
          Fintype.card (SimpleExpansion.Left B (Fin (F.n k))) ∧
      ((SimpleExpansion.canonicalMatching B (F.host k) J).card : ℚ) /
          Fintype.card (SimpleExpansion.Left B (Fin (F.n k))) ≤
        blueprintValueRat B + B.P * F.loss := by
  rw [SimpleExpansion.canonical_density_eq_blueprintValue_mul]
  simpa using mul_pow_close (blueprintValueRat_nonneg B) (blueprintValueRat_le_one B)
    F.loss_nonneg F.loss_lt_one.le
    (F.one_sub_loss_le_relative_density k) (F.relative_density_le_one k) B.P

end DenseERSSequence

end ERSFamily

end Formal.Streaming
