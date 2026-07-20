import SemiStreamingMatching.Proofs.Framework.FiniteProbability
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Complex.ExponentialBounds

open scoped BigOperators

namespace Formal.Streaming

namespace FiniteDist

variable {Ω A E : Type*} [Fintype Ω] [Fintype A] [Fintype E] [DecidableEq E]

noncomputable def entropy (P : FiniteDist Ω) : ℝ :=
  ∑ ω, Real.negMulLog (P.mass ω)

noncomputable def relEntropy (P Q : FiniteDist Ω) : ℝ :=
  ∑ ω, P.mass ω * Real.log (P.mass ω / Q.mass ω)

theorem mass_le_one (P : FiniteDist Ω) (ω : Ω) : P.mass ω ≤ 1 := by
  rw [← P.sum_mass]
  exact Finset.single_le_sum (fun i _ => P.mass_nonneg i) (Finset.mem_univ ω)

theorem entropy_nonneg (P : FiniteDist Ω) : 0 ≤ P.entropy := by
  unfold entropy
  exact Finset.sum_nonneg fun ω _ =>
    Real.negMulLog_nonneg (P.mass_nonneg ω) (P.mass_le_one ω)

theorem entropy_uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (FiniteDist.uniform Ω).entropy = Real.log (Fintype.card Ω) := by
  unfold entropy
  simp only [uniform_mass, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  unfold Real.negMulLog
  rw [Real.log_div (by norm_num) hcard, Real.log_one]
  field_simp

noncomputable def conditionalEntropy [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A) : ℝ :=
  ∑ a, (P.map f).mass a * (P.conditional f a).entropy

private theorem entropy_fiber_of_pos [DecidableEq A] (P : FiniteDist Ω)
    (f : Ω → A) (a : A) (ha : 0 < (P.map f).mass a) :
    Real.negMulLog ((P.map f).mass a) +
        (P.map f).mass a * (P.conditional f a).entropy =
      ∑ ω with f ω = a, Real.negMulLog (P.mass ω) := by
  classical
  let pa := (P.map f).mass a
  have hpa : 0 < pa := ha
  have hsum : (∑ ω with f ω = a, P.mass ω / pa) = 1 := by
    rw [← Finset.sum_div, ← map_mass]
    exact div_self hpa.ne'
  have hcond : (P.conditional f a).entropy =
      ∑ ω with f ω = a, Real.negMulLog (P.mass ω / pa) := by
    rw [P.conditional_eq_conditionMap f a ha]
    unfold entropy
    change (∑ ω, Real.negMulLog
      (if f ω = a then P.mass ω / pa else 0)) = _
    simp only [apply_ite, Real.negMulLog_zero]
    rw [Finset.sum_ite]
    simp
  rw [hcond]
  change Real.negMulLog pa + pa *
      (∑ ω with f ω = a, Real.negMulLog (P.mass ω / pa)) = _
  calc
    Real.negMulLog pa + pa *
        (∑ ω with f ω = a, Real.negMulLog (P.mass ω / pa)) =
      (∑ ω with f ω = a, P.mass ω / pa) * Real.negMulLog pa +
        pa * (∑ ω with f ω = a, Real.negMulLog (P.mass ω / pa)) := by rw [hsum, one_mul]
    _ = ∑ ω with f ω = a,
        ((P.mass ω / pa) * Real.negMulLog pa +
          pa * Real.negMulLog (P.mass ω / pa)) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ ω with f ω = a, Real.negMulLog (P.mass ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [← Real.negMulLog_mul]
      congr 1
      field_simp [hpa.ne']

private theorem entropy_fiber_of_zero [DecidableEq A] (P : FiniteDist Ω)
    (f : Ω → A) (a : A) (ha : (P.map f).mass a = 0) :
    ∑ ω with f ω = a, Real.negMulLog (P.mass ω) = 0 := by
  apply Finset.sum_eq_zero
  intro ω hω
  have hle : P.mass ω ≤ (P.map f).mass a := by
    rw [map_mass]
    exact Finset.single_le_sum (fun x _ => P.mass_nonneg x) hω
  have hm : P.mass ω = 0 := by
    apply le_antisymm
    · rw [ha] at hle
      exact hle
    · exact P.mass_nonneg ω
  simp [hm]

theorem entropy_chain [DecidableEq A] (P : FiniteDist Ω) (f : Ω → A) :
    P.entropy = (P.map f).entropy + P.conditionalEntropy f := by
  classical
  unfold entropy
  calc
    (∑ ω, Real.negMulLog (P.mass ω)) =
        ∑ a, ∑ ω with f ω = a, Real.negMulLog (P.mass ω) :=
      (Finset.sum_fiberwise (Finset.univ : Finset Ω) f
        (fun ω => Real.negMulLog (P.mass ω))).symm
    _ = ∑ a, (Real.negMulLog ((P.map f).mass a) +
        (P.map f).mass a * (P.conditional f a).entropy) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha0 : (P.map f).mass a = 0
        · rw [entropy_fiber_of_zero P f a ha0, ha0, Real.negMulLog_zero,
            zero_mul, zero_add]
        · exact (entropy_fiber_of_pos P f a
            (lt_of_le_of_ne ((P.map f).mass_nonneg a) (Ne.symm ha0))).symm
    _ = (∑ a, Real.negMulLog ((P.map f).mass a)) + P.conditionalEntropy f := by
      unfold conditionalEntropy
      rw [Finset.sum_add_distrib]

theorem relEntropy_nonneg (P Q : FiniteDist Ω)
    (hsupp : ∀ ω, 0 < P.mass ω → 0 < Q.mass ω) :
    0 ≤ P.relEntropy Q := by
  have hterm : ∀ ω, P.mass ω - Q.mass ω ≤
      P.mass ω * Real.log (P.mass ω / Q.mass ω) := by
    intro ω
    by_cases hp : P.mass ω = 0
    · simp [hp, Q.mass_nonneg]
    · have hp' : 0 < P.mass ω := lt_of_le_of_ne (P.mass_nonneg ω) (Ne.symm hp)
      have hq' : 0 < Q.mass ω := hsupp ω hp'
      have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
      have hlogeq : Real.log (Q.mass ω / P.mass ω) =
          -Real.log (P.mass ω / Q.mass ω) := by
        rw [Real.log_div hq'.ne' hp'.ne', Real.log_div hp'.ne' hq'.ne']
        ring
      rw [hlogeq] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hp'.le
      field_simp [hp, hq'.ne'] at hmul ⊢
      nlinarith
  unfold relEntropy
  calc
    0 = ∑ ω, (P.mass ω - Q.mass ω) := by
      rw [Finset.sum_sub_distrib, P.sum_mass, Q.sum_mass, sub_self]
    _ ≤ _ := Finset.sum_le_sum fun ω _ => hterm ω

theorem entropy_le_log_card [Nonempty Ω] (P : FiniteDist Ω) :
    P.entropy ≤ Real.log (Fintype.card Ω) := by
  let U := FiniteDist.uniform Ω
  have hUpos : ∀ ω, 0 < U.mass ω := by
    intro ω
    dsimp only [U]
    rw [uniform_mass]
    positivity
  have hKL : 0 ≤ P.relEntropy U := P.relEntropy_nonneg U (fun ω _ => hUpos ω)
  have hid : P.relEntropy U = Real.log (Fintype.card Ω) - P.entropy := by
    unfold relEntropy entropy
    calc
      (∑ ω, P.mass ω * Real.log (P.mass ω / U.mass ω)) =
          ∑ ω, (P.mass ω * Real.log (Fintype.card Ω) -
            Real.negMulLog (P.mass ω)) := by
              apply Finset.sum_congr rfl
              intro ω _
              by_cases hp0 : P.mass ω = 0
              · simp [hp0]
              · have hp : 0 < P.mass ω :=
                  lt_of_le_of_ne (P.mass_nonneg ω) (Ne.symm hp0)
                have hcard : 0 < (Fintype.card Ω : ℝ) := by positivity
                have hquot : P.mass ω / U.mass ω =
                    P.mass ω * Fintype.card Ω := by
                  dsimp only [U]
                  rw [uniform_mass]
                  field_simp
                rw [hquot, Real.log_mul hp.ne' hcard.ne']
                unfold Real.negMulLog
                ring
      _ = Real.log (Fintype.card Ω) - P.entropy := by
            unfold entropy
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_mass]
            ring
  linarith

noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1 - p)

theorem binaryEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryEntropy p := by
  unfold binaryEntropy
  exact add_nonneg (Real.negMulLog_nonneg hp0 hp1)
    (Real.negMulLog_nonneg (sub_nonneg.mpr hp1) (by linarith))

noncomputable def bernoulliKL (p d : ℝ) : ℝ :=
  p * Real.log (p / d) + (1 - p) * Real.log ((1 - p) / (1 - d))

noncomputable def marginal (P : FiniteDist (Finset E)) (e : E) : ℝ :=
  P.prob (fun D => e ∈ D)

theorem marginal_nonneg (P : FiniteDist (Finset E)) (e : E) : 0 ≤ P.marginal e :=
  P.prob_nonneg _

theorem marginal_le_one (P : FiniteDist (Finset E)) (e : E) : P.marginal e ≤ 1 :=
  P.prob_le_one _

theorem one_sub_marginal (P : FiniteDist (Finset E)) (e : E) :
    1 - P.marginal e = P.prob (fun D => e ∉ D) := by
  rw [P.prob_compl (fun D : Finset E => e ∈ D)]
  rfl

noncomputable def finsetProduct (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) : FiniteDist (Finset E) where
  mass D := (∏ e in D, p e) * ∏ e in (Finset.univ \ D), (1 - p e)
  mass_nonneg D := mul_nonneg
    (Finset.prod_nonneg fun e _ => hp0 e)
    (Finset.prod_nonneg fun e _ => sub_nonneg.mpr (hp1 e))
  sum_mass := by
    classical
    have h := Finset.prod_add p (fun e => 1 - p e) (Finset.univ : Finset E)
    simp only [add_sub_cancel, Finset.prod_const_one, Finset.powerset_univ] at h
    simpa using h.symm

@[simp] theorem finsetProduct_mass (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (D : Finset E) :
    (finsetProduct p hp0 hp1).mass D =
      (∏ e in D, p e) * ∏ e in (Finset.univ \ D), (1 - p e) := rfl

private theorem marginal_pos_of_mass_pos (P : FiniteDist (Finset E))
    {D : Finset E} {e : E} (hD : 0 < P.mass D) (he : e ∈ D) :
    0 < P.marginal e := by
  unfold marginal prob
  exact hD.trans_le (Finset.single_le_sum (fun T _ => P.mass_nonneg T) (by simp [he]))

private theorem one_sub_marginal_pos_of_mass_pos (P : FiniteDist (Finset E))
    {D : Finset E} {e : E} (hD : 0 < P.mass D) (he : e ∉ D) :
    0 < 1 - P.marginal e := by
  rw [P.one_sub_marginal e]
  unfold prob
  exact hD.trans_le (Finset.single_le_sum (fun T _ => P.mass_nonneg T) (by simp [he]))

private theorem product_support (P : FiniteDist (Finset E)) (D : Finset E)
    (hD : 0 < P.mass D) :
    0 < (finsetProduct (P.marginal) P.marginal_nonneg P.marginal_le_one).mass D := by
  rw [finsetProduct_mass]
  apply mul_pos
  · exact Finset.prod_pos fun e he => marginal_pos_of_mass_pos P hD he
  · exact Finset.prod_pos fun e he =>
      one_sub_marginal_pos_of_mass_pos P hD (by simpa using (Finset.mem_sdiff.1 he).2)

private theorem log_product_mass (P : FiniteDist (Finset E)) (D : Finset E)
    (hD : 0 < P.mass D) :
    Real.log ((finsetProduct (P.marginal) P.marginal_nonneg P.marginal_le_one).mass D) =
      (∑ e in D, Real.log (P.marginal e)) +
        ∑ e in (Finset.univ \ D), Real.log (1 - P.marginal e) := by
  have hleft : 0 < ∏ e in D, P.marginal e :=
    Finset.prod_pos fun e he => marginal_pos_of_mass_pos P hD he
  have hright : 0 < ∏ e in (Finset.univ \ D), (1 - P.marginal e) :=
    Finset.prod_pos fun e he => one_sub_marginal_pos_of_mass_pos P hD
      (by simpa using (Finset.mem_sdiff.1 he).2)
  rw [finsetProduct_mass, Real.log_mul hleft.ne' hright.ne',
    Real.log_prod D (P.marginal) (fun e he => (marginal_pos_of_mass_pos P hD he).ne'),
    Real.log_prod (Finset.univ \ D) (fun e => 1 - P.marginal e)
      (fun e he => (one_sub_marginal_pos_of_mass_pos P hD
        (by simpa using (Finset.mem_sdiff.1 he).2)).ne')]

private theorem sum_log_score (P : FiniteDist (Finset E)) (e : E) :
    (∑ D, P.mass D * (if e ∈ D then Real.log (P.marginal e)
      else Real.log (1 - P.marginal e))) =
      P.marginal e * Real.log (P.marginal e) +
        (1 - P.marginal e) * Real.log (1 - P.marginal e) := by
  classical
  simp_rw [mul_ite]
  rw [Finset.sum_ite]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  change P.marginal e * Real.log (P.marginal e) +
      P.prob (fun D : Finset E => e ∉ D) * Real.log (1 - P.marginal e) = _
  rw [← P.one_sub_marginal e]

private theorem crossEntropy_product (P : FiniteDist (Finset E)) :
    -(∑ D, P.mass D *
        Real.log ((finsetProduct (P.marginal) P.marginal_nonneg P.marginal_le_one).mass D)) =
      ∑ e, binaryEntropy (P.marginal e) := by
  classical
  have hpoint : ∀ D : Finset E,
      P.mass D * Real.log
          ((finsetProduct (P.marginal) P.marginal_nonneg P.marginal_le_one).mass D) =
        P.mass D * ∑ e, (if e ∈ D then Real.log (P.marginal e)
          else Real.log (1 - P.marginal e)) := by
    intro D
    by_cases hD0 : P.mass D = 0
    · simp [hD0]
    · have hD : 0 < P.mass D := lt_of_le_of_ne (P.mass_nonneg D) (Ne.symm hD0)
      rw [log_product_mass P D hD]
      congr 1
      have hfilter : (Finset.univ : Finset E).filter (fun e => e ∈ D) = D := by
        ext e
        simp
      have hfilter_not : (Finset.univ : Finset E).filter (fun e => e ∉ D) =
          Finset.univ \ D := by
        ext e
        simp
      rw [Finset.sum_ite]
      rw [hfilter, hfilter_not]
  simp_rw [hpoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_log_score]
  unfold binaryEntropy Real.negMulLog
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem entropy_le_sum_binaryEntropy (P : FiniteDist (Finset E)) :
    P.entropy ≤ ∑ e, binaryEntropy (P.marginal e) := by
  let Q := finsetProduct (P.marginal) P.marginal_nonneg P.marginal_le_one
  have hKL : 0 ≤ P.relEntropy Q := P.relEntropy_nonneg Q (product_support P)
  have hid : P.relEntropy Q =
      -P.entropy - ∑ D, P.mass D * Real.log (Q.mass D) := by
    dsimp only [Q]
    unfold relEntropy
    calc
      (∑ D, P.mass D * Real.log (P.mass D /
          (finsetProduct P.marginal P.marginal_nonneg P.marginal_le_one).mass D)) =
          ∑ D, (-Real.negMulLog (P.mass D) - P.mass D *
            Real.log ((finsetProduct P.marginal P.marginal_nonneg
              P.marginal_le_one).mass D)) := by
            apply Finset.sum_congr rfl
            intro D _
            by_cases hD0 : P.mass D = 0
            · simp [hD0]
            · have hD : 0 < P.mass D :=
                lt_of_le_of_ne (P.mass_nonneg D) (Ne.symm hD0)
              have hQ : 0 < (finsetProduct (P.marginal) P.marginal_nonneg
                P.marginal_le_one).mass D := product_support P D hD
              rw [Real.log_div hD.ne' hQ.ne']
              simp only [Real.negMulLog]
              ring
      _ = -P.entropy - ∑ D, P.mass D * Real.log
          ((finsetProduct P.marginal P.marginal_nonneg P.marginal_le_one).mass D) := by
            unfold entropy
            rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hid] at hKL
  dsimp only [Q] at hKL
  have hcross := crossEntropy_product P
  linarith

noncomputable def conditionalMarginal [DecidableEq A] (P : FiniteDist (Finset E))
    (f : Finset E → A) (a : A) (e : E) : ℝ :=
  (P.conditional f a).marginal e

theorem conditionalEntropy_le_sum_binary [DecidableEq A]
    (P : FiniteDist (Finset E)) (f : Finset E → A) :
    P.conditionalEntropy f ≤
      ∑ a, (P.map f).mass a * ∑ e, binaryEntropy (P.conditionalMarginal f a e) := by
  unfold conditionalEntropy conditionalMarginal
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (entropy_le_sum_binaryEntropy (P.conditional f a)) ((P.map f).mass_nonneg a)

theorem sum_mass_mul_conditionalMarginal [DecidableEq A]
    (P : FiniteDist (Finset E)) (f : Finset E → A) (e : E) :
    (∑ a, (P.map f).mass a * P.conditionalMarginal f a e) = P.marginal e := by
  unfold conditionalMarginal marginal
  exact P.sum_map_mass_mul_conditional_prob f (fun D => e ∈ D)

noncomputable def coordinateInformation [DecidableEq A]
    (P : FiniteDist (Finset E)) (f : Finset E → A) : ℝ :=
  ∑ a, (P.map f).mass a *
    ∑ e, bernoulliKL (P.conditionalMarginal f a e) (P.marginal e)

private theorem bernoulliKL_expand {p d : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 < d) (hd1 : d < 1) :
    bernoulliKL p d = -binaryEntropy p - p * Real.log d -
      (1 - p) * Real.log (1 - d) := by
  unfold bernoulliKL binaryEntropy Real.negMulLog
  by_cases hpzero : p = 0
  · simp [hpzero, Real.log_one, hd1.ne, hd0.ne']
  by_cases hpone : p = 1
  · simp [hpone, Real.log_one, hd1.ne, hd0.ne']
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
  have hp' : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp1 hpone)
  rw [Real.log_div hp.ne' hd0.ne', Real.log_div hp'.ne' (sub_pos.mpr hd1).ne']
  ring

theorem coordinateInformation_eq [DecidableEq A]
    (P : FiniteDist (Finset E)) (f : Finset E → A)
    (hpos : ∀ e, 0 < P.marginal e) (hlt : ∀ e, P.marginal e < 1) :
    P.coordinateInformation f =
      (∑ e, binaryEntropy (P.marginal e)) -
        ∑ a, (P.map f).mass a *
          ∑ e, binaryEntropy (P.conditionalMarginal f a e) := by
  classical
  unfold coordinateInformation
  have hexpand : ∀ a e,
      bernoulliKL (P.conditionalMarginal f a e) (P.marginal e) =
        -binaryEntropy (P.conditionalMarginal f a e) -
          P.conditionalMarginal f a e * Real.log (P.marginal e) -
          (1 - P.conditionalMarginal f a e) * Real.log (1 - P.marginal e) := by
    intro a e
    exact bernoulliKL_expand
      ((P.conditional f a).marginal_nonneg e)
      ((P.conditional f a).marginal_le_one e) (hpos e) (hlt e)
  simp_rw [hexpand, Finset.mul_sum]
  have hswap : (∑ a, ∑ e,
      (P.map f).mass a * binaryEntropy (P.conditionalMarginal f a e)) =
      ∑ e, ∑ a, (P.map f).mass a *
        binaryEntropy (P.conditionalMarginal f a e) := Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hmass : ∑ a, (P.map f).mass a = 1 := (P.map f).sum_mass
  have hmean := P.sum_mass_mul_conditionalMarginal f e
  simp_rw [mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [← mul_assoc]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul]
  unfold binaryEntropy Real.negMulLog
  have hone : (∑ a, (P.map f).mass a *
      (1 - P.conditionalMarginal f a e)) = 1 - P.marginal e := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hmass, hmean]
  rw [hmean, hone]
  ring

theorem coordinateInformation_le [DecidableEq A]
    (P : FiniteDist (Finset E)) (f : Finset E → A)
    (hpos : ∀ e, 0 < P.marginal e) (hlt : ∀ e, P.marginal e < 1) :
    P.coordinateInformation f ≤
      (P.map f).entropy + (∑ e, binaryEntropy (P.marginal e)) - P.entropy := by
  rw [P.coordinateInformation_eq f hpos hlt]
  have hcond := P.conditionalEntropy_le_sum_binary f
  have hchain := P.entropy_chain f
  linarith

end FiniteDist

namespace Entropy

theorem negMulLog_le_nine_twentieth {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.negMulLog x ≤ 9 / 20 := by
  by_cases hxzero : x = 0
  · simp [hxzero]
    norm_num
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
  have hypos : 0 < (1 / x) / 4 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hypos
  have hlog2 : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlog4 : Real.log 4 < 7 / 5 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hrewrite : Real.log ((1 / x) / 4) = Real.log (1 / x) - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  rw [hrewrite] at hlog
  have hloginv : Real.log (1 / x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  rw [hloginv] at hlog
  unfold Real.negMulLog
  have hxnonneg : 0 ≤ x := hxpos.le
  have hmul := mul_le_mul_of_nonneg_left (show -Real.log x ≤ 1 / x / 4 - 1 + 7 / 5 by linarith) hxnonneg
  calc
    -x * Real.log x = x * (-Real.log x) := by ring
    _ ≤ x * (1 / x / 4 - 1 + 7 / 5) := hmul
    _ = 1 / 4 + (2 / 5) * x := by
      field_simp [hxzero]
      all_goals ring
    _ ≤ 9 / 20 := by nlinarith

theorem bernoulliKL_ge_one_twentieth {p d : ℝ}
    (hd0 : 0 < d) (hdhalf : d ≤ 1 / 2) (hp0 : 0 ≤ p) (hp : p ≤ d / 2) :
    d / 20 ≤ FiniteDist.bernoulliKL p d := by
  have hd1 : d < 1 := lt_of_le_of_lt hdhalf (by norm_num)
  have hp1 : p < 1 := lt_of_le_of_lt hp (by linarith)
  have hsecond : d - p ≤
      (1 - p) * Real.log ((1 - p) / (1 - d)) := by
    have hratio : 0 < (1 - d) / (1 - p) := div_pos (by linarith) (by linarith)
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hlogeq : Real.log ((1 - d) / (1 - p)) =
        -Real.log ((1 - p) / (1 - d)) := by
      rw [Real.log_div (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)]
      ring
    rw [hlogeq] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 - p by linarith)
    field_simp [show 1 - p ≠ 0 by linarith, show 1 - d ≠ 0 by linarith] at hmul ⊢
    nlinarith
  have hpterm : -(9 / 20) * d ≤ p * Real.log (p / d) := by
    by_cases hpzero : p = 0
    · simp [hpzero, hd0.le]
    · have hx0 : 0 ≤ p / d := div_nonneg hp0 hd0.le
      have hxhalf : p / d ≤ 1 / 2 := (div_le_iff hd0).2 (by linarith)
      have hneg := negMulLog_le_nine_twentieth hx0 hxhalf
      unfold Real.negMulLog at hneg
      have hmul := mul_le_mul_of_nonneg_left hneg hd0.le
      calc
        -(9 / 20) * d ≤ d * ((p / d) * Real.log (p / d)) := by nlinarith
        _ = p * Real.log (p / d) := by field_simp [hd0.ne']
  unfold FiniteDist.bernoulliKL
  nlinarith

theorem bernoulliKL_nonneg {p d : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 < d) (hd1 : d < 1) :
    0 ≤ FiniteDist.bernoulliKL p d := by
  have hterm : ∀ x y : ℝ, 0 ≤ x → 0 < y →
      x - y ≤ x * Real.log (x / y) := by
    intro x y hx hy
    by_cases hxzero : x = 0
    · simp [hxzero, hy.le]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hy hxpos)
      have hlogeq : Real.log (y / x) = -Real.log (x / y) := by
        rw [Real.log_div hy.ne' hxpos.ne', Real.log_div hxpos.ne' hy.ne']
        ring
      rw [hlogeq] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hx
      field_simp [hxzero, hy.ne'] at hmul ⊢
      nlinarith
  have h₁ := hterm p d hp0 hd0
  have h₂ := hterm (1 - p) (1 - d) (by linarith) (by linarith)
  unfold FiniteDist.bernoulliKL
  linarith

end Entropy

end Formal.Streaming
