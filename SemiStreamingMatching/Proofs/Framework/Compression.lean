import SemiStreamingMatching.Proofs.Framework.Entropy
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

namespace Formal.Streaming

namespace Compression

variable {E M : Type*} [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

abbrev Scheme (E M : Type*) := Finset E → M

def Belong (P : FiniteDist (Finset E)) (Φ : Scheme E M) (δ : ℝ) (msg : M) (e : E) : Prop :=
  0 < (P.map Φ).mass msg ∧ P.conditionalMarginal Φ msg e ≤ δ / 2

noncomputable instance instDecidableBelong (P : FiniteDist (Finset E))
    (Φ : Scheme E M) (δ : ℝ) (msg : M) (e : E) :
    Decidable (Belong P Φ δ msg e) := Classical.propDecidable _

noncomputable def belongSet (P : FiniteDist (Finset E)) (Φ : Scheme E M)
    (δ : ℝ) (msg : M) : Finset E :=
  by
    classical
    exact Finset.univ.filter (Belong P Φ δ msg)

noncomputable def expectedBelong (P : FiniteDist (Finset E)) (Φ : Scheme E M)
    (δ : ℝ) : ℝ :=
  (P.map Φ).expect (fun msg => ((belongSet P Φ δ msg).card : ℝ))

theorem expectedBelong_eq_input_expect (P : FiniteDist (Finset E)) (Φ : Scheme E M)
    (δ : ℝ) :
    expectedBelong P Φ δ =
      P.expect (fun D => ((belongSet P Φ δ (Φ D)).card : ℝ)) := by
  exact (P.expect_map Φ _)

private theorem card_belong_eq_sum (P : FiniteDist (Finset E)) (Φ : Scheme E M)
    (δ : ℝ) (msg : M) :
    ((belongSet P Φ δ msg).card : ℝ) =
      ∑ e, if Belong P Φ δ msg e then 1 else 0 := by
  classical
  unfold belongSet
  norm_cast
  exact Finset.card_filter (Belong P Φ δ msg) Finset.univ

theorem expectedBelong_mul_le_coordinateInformation
    (P : FiniteDist (Finset E)) (Φ : Scheme E M) {δ : ℝ}
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmarg : ∀ e, P.marginal e = δ) :
    expectedBelong P Φ δ * (δ / 20) ≤ P.coordinateInformation Φ := by
  classical
  unfold expectedBelong FiniteDist.expect FiniteDist.coordinateInformation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro msg _
  calc
    ((P.map Φ).mass msg * ((belongSet P Φ δ msg).card : ℝ)) * (δ / 20) =
        (P.map Φ).mass msg *
          (((belongSet P Φ δ msg).card : ℝ) * (δ / 20)) := by ring
    _ ≤ (P.map Φ).mass msg * ∑ e,
        FiniteDist.bernoulliKL (P.conditionalMarginal Φ msg e) (P.marginal e) :=
      mul_le_mul_of_nonneg_left (by
        rw [card_belong_eq_sum, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro e _
        by_cases he : Belong P Φ δ msg e
        · rw [if_pos he, one_mul]
          rw [hmarg e]
          exact Entropy.bernoulliKL_ge_one_twentieth hδ0 hδhalf
            ((P.conditional Φ msg).marginal_nonneg e) he.2
        · rw [if_neg he, zero_mul]
          rw [hmarg e]
          exact Entropy.bernoulliKL_nonneg
            ((P.conditional Φ msg).marginal_nonneg e)
            ((P.conditional Φ msg).marginal_le_one e) hδ0
            (lt_of_le_of_lt hδhalf (by norm_num))) ((P.map Φ).mass_nonneg msg)

theorem expectedBelong_le_entropy
    (P : FiniteDist (Finset E)) (Φ : Scheme E M) {δ : ℝ}
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmarg : ∀ e, P.marginal e = δ) :
    expectedBelong P Φ δ ≤
      (20 / δ) * ((P.map Φ).entropy +
        ((Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ - P.entropy)) := by
  have hlower := expectedBelong_mul_le_coordinateInformation P Φ hδ0 hδhalf hmarg
  have hupper := P.coordinateInformation_le Φ
    (fun e => by rw [hmarg e]; exact hδ0)
    (fun e => by rw [hmarg e]; exact lt_of_le_of_lt hδhalf (by norm_num))
  have hsum : (∑ e, FiniteDist.binaryEntropy (P.marginal e)) =
      (Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ := by
    simp_rw [hmarg]
    simp
  rw [hsum] at hupper
  rw [show (20 / δ) * ((P.map Φ).entropy +
      ((Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ - P.entropy)) =
      (20 * ((P.map Φ).entropy +
        ((Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ - P.entropy))) / δ by
        field_simp [hδ0.ne']]
  apply (le_div_iff hδ0).2
  nlinarith

theorem expectedBelong_le_card
    [Nonempty M] (P : FiniteDist (Finset E)) (Φ : Scheme E M) {δ : ℝ}
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmarg : ∀ e, P.marginal e = δ) :
    expectedBelong P Φ δ ≤
      (20 / δ) * (Real.log (Fintype.card M) +
        ((Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ - P.entropy)) := by
  have h := expectedBelong_le_entropy P Φ hδ0 hδhalf hmarg
  have hmsg := (P.map Φ).entropy_le_log_card
  have hfactor : 0 ≤ 20 / δ := by positivity
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hfactor)

theorem expectedBelong_le_bits
    [Nonempty M] (P : FiniteDist (Finset E)) (Φ : Scheme E M) (s : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmarg : ∀ e, P.marginal e = δ)
    (hcard : Fintype.card M ≤ 2 ^ s) :
    expectedBelong P Φ δ ≤
      (20 / δ) * ((s : ℝ) * Real.log 2 +
        ((Fintype.card E : ℝ) * FiniteDist.binaryEntropy δ - P.entropy)) := by
  have h := expectedBelong_le_card P Φ hδ0 hδhalf hmarg
  have hMpos : 0 < (Fintype.card M : ℝ) := by positivity
  have hcast : (Fintype.card M : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hlog := Real.log_le_log hMpos hcast
  have hpow : Real.log ((2 ^ s : ℕ) : ℝ) = (s : ℝ) * Real.log 2 := by
    have hc : (((2 ^ s : ℕ) : ℝ)) = (2 : ℝ) ^ s := by exact_mod_cast rfl
    rw [hc, Real.log_pow]
  rw [hpow] at hlog
  have hfactor : 0 ≤ 20 / δ := by positivity
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hfactor)

section FixedCard

variable {q : ℕ}

noncomputable def fixedCardDist (q : ℕ) (hq : q ≤ Fintype.card E) :
    FiniteDist (Finset E) where
  mass D := if D.card = q then (1 : ℝ) / (Nat.choose (Fintype.card E) q : ℝ) else 0
  mass_nonneg D := by
    dsimp
    split <;> positivity
  sum_mass := by
    classical
    simp_rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.univ_filter_card_eq, Finset.card_powersetCard]
    have hchoose : (Nat.choose (Fintype.card E) q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hq).ne'
    field_simp

@[simp] theorem fixedCardDist_mass (q : ℕ) (hq : q ≤ Fintype.card E) (D : Finset E) :
    (fixedCardDist (E := E) q hq).mass D =
      if D.card = q then (1 : ℝ) / (Nat.choose (Fintype.card E) q : ℝ) else 0 := rfl

def fixedCardFiber (q : ℕ) (Φ : Scheme E M) (msg : M) : Finset (Finset E) :=
  Finset.univ.filter fun D => D.card = q ∧ Φ D = msg

def fixedCardDeletedFiber (q : ℕ) (Φ : Scheme E M) (msg : M)
    (e : E) : Finset (Finset E) :=
  (fixedCardFiber q Φ msg).filter fun D => e ∈ D

theorem fixedCardDist_map_mass (q : ℕ) (hq : q ≤ Fintype.card E)
    (Φ : Scheme E M) (msg : M) :
    ((fixedCardDist (E := E) q hq).map Φ).mass msg =
      ((fixedCardFiber q Φ msg).card : ℝ) /
        Nat.choose (Fintype.card E) q := by
  classical
  rw [FiniteDist.map_mass]
  simp_rw [fixedCardDist_mass]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
  have hfilter :
      ((Finset.univ.filter fun D : Finset E => Φ D = msg).filter
          fun D => D.card = q) = fixedCardFiber q Φ msg := by
    ext D
    simp [fixedCardFiber, and_comm]
  rw [hfilter]
  ring

private theorem fixedCardDist_joint_prob (q : ℕ) (hq : q ≤ Fintype.card E)
    (Φ : Scheme E M) (msg : M) (e : E) :
    (fixedCardDist (E := E) q hq).prob (fun D => e ∈ D ∧ Φ D = msg) =
      ((fixedCardDeletedFiber q Φ msg e).card : ℝ) /
        Nat.choose (Fintype.card E) q := by
  classical
  unfold FiniteDist.prob
  simp_rw [fixedCardDist_mass]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
  have hfilter :
      ((Finset.univ.filter fun D : Finset E => e ∈ D ∧ Φ D = msg).filter
          fun D => D.card = q) = fixedCardDeletedFiber q Φ msg e := by
    ext D
    simp [fixedCardDeletedFiber, fixedCardFiber, and_assoc, and_left_comm,
      and_comm]
  rw [hfilter]
  ring

theorem fixedCardDist_conditionalMarginal_eq_card_ratio
    (q : ℕ) (hq : q ≤ Fintype.card E) (Φ : Scheme E M) (msg : M) (e : E)
    (hmsg : 0 < (fixedCardFiber q Φ msg).card) :
    (fixedCardDist (E := E) q hq).conditionalMarginal Φ msg e =
      ((fixedCardDeletedFiber q Φ msg e).card : ℝ) /
        (fixedCardFiber q Φ msg).card := by
  let P := fixedCardDist (E := E) q hq
  have hchoose : 0 < (Nat.choose (Fintype.card E) q : ℝ) := by
    exact_mod_cast Nat.choose_pos hq
  have hfiber : 0 < ((fixedCardFiber q Φ msg).card : ℝ) := by
    exact_mod_cast hmsg
  have hmass : 0 < (P.map Φ).mass msg := by
    rw [fixedCardDist_map_mass]
    exact div_pos hfiber hchoose
  unfold FiniteDist.conditionalMarginal FiniteDist.marginal
  rw [FiniteDist.conditional_prob P Φ msg hmass]
  rw [fixedCardDist_joint_prob, fixedCardDist_map_mass]
  field_simp [hchoose.ne', hfiber.ne']

theorem mem_belongSet_fixedCard_iff
    (q : ℕ) (hq : q ≤ Fintype.card E) (Φ : Scheme E M) (msg : M) (e : E)
    (δ : ℝ) :
    e ∈ belongSet (fixedCardDist (E := E) q hq) Φ δ msg ↔
      0 < (fixedCardFiber q Φ msg).card ∧
        ((fixedCardDeletedFiber q Φ msg e).card : ℝ) /
            (fixedCardFiber q Φ msg).card ≤ δ / 2 := by
  classical
  have hchoose : 0 < (Nat.choose (Fintype.card E) q : ℝ) := by
    exact_mod_cast Nat.choose_pos hq
  have hmass_iff :
      0 < (((fixedCardDist (E := E) q hq).map Φ).mass msg) ↔
        0 < (fixedCardFiber q Φ msg).card := by
    rw [fixedCardDist_map_mass]
    constructor
    · intro h
      have hnum : 0 < ((fixedCardFiber q Φ msg).card : ℝ) := by
        rcases div_pos_iff.mp h with hpos | hneg
        · exact hpos.1
        · linarith
      exact_mod_cast hnum
    · intro h
      exact div_pos (by exact_mod_cast h) hchoose
  simp only [belongSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Belong
  constructor
  · intro h
    have hmsg := hmass_iff.mp h.1
    refine ⟨hmsg, ?_⟩
    rw [← fixedCardDist_conditionalMarginal_eq_card_ratio q hq Φ msg e hmsg]
    exact h.2
  · intro h
    refine ⟨hmass_iff.mpr h.1, ?_⟩
    rw [fixedCardDist_conditionalMarginal_eq_card_ratio q hq Φ msg e h.1]
    exact h.2

theorem fixedCardDist_entropy (q : ℕ) (hq : q ≤ Fintype.card E) :
    (fixedCardDist (E := E) q hq).entropy =
      Real.log (Nat.choose (Fintype.card E) q) := by
  classical
  unfold FiniteDist.entropy
  simp_rw [fixedCardDist_mass, apply_ite, Real.negMulLog_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.univ_filter_card_eq, Finset.card_powersetCard]
  have hchoose : (Nat.choose (Fintype.card E) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  unfold Real.negMulLog
  rw [Real.log_div (by norm_num) hchoose, Real.log_one]
  field_simp

private theorem card_fixed_containing (e : E) (q : ℕ) (hq0 : 0 < q) :
    ((Finset.univ : Finset (Finset E)).filter (fun D => D.card = q ∧ e ∈ D)).card =
      Nat.choose (Fintype.card E - 1) (q - 1) := by
  classical
  let source := (Finset.univ.erase e).powersetCard (q - 1)
  have himage : (Finset.univ : Finset (Finset E)).filter
      (fun D => D.card = q ∧ e ∈ D) = source.image (insert e) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powersetCard, source]
    constructor
    · intro h
      refine ⟨D.erase e, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact (Finset.mem_erase.1 hx).1
        · rw [Finset.card_erase_of_mem h.2, h.1]
      · exact Finset.insert_erase h.2
    · rintro ⟨D, hD, rfl⟩
      have heD : e ∉ D := fun he => (Finset.mem_erase.1 (hD.1 he)).1 rfl
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq0
      rw [Finset.card_insert_of_not_mem heD, hD.2, hqsub]
  rw [himage]
  have hinj : Set.InjOn (insert e) (↑source : Set (Finset E)) := by
    intro A hA B hB hab
    have heA : e ∉ A := by
      intro he
      exact (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hA).1 he)).1 rfl
    have heB : e ∉ B := by
      intro he
      exact (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hB).1 he)).1 rfl
    simpa [heA, heB] using congrArg (Finset.erase · e) hab
  rw [(Finset.card_image_iff.mpr hinj), Finset.card_powersetCard]
  congr 1
  simp

theorem fixedCardDist_marginal (e : E) (q : ℕ) (hq0 : 0 < q)
    (hqlt : q < Fintype.card E) :
    (fixedCardDist (E := E) q hqlt.le).marginal e =
      (q : ℝ) / Fintype.card E := by
  classical
  unfold FiniteDist.marginal FiniteDist.prob
  simp_rw [fixedCardDist_mass]
  change (∑ D : Finset E with e ∈ D,
      if D.card = q then 1 / (Nat.choose (Fintype.card E) q : ℝ) else 0) = _
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter : ((Finset.univ : Finset (Finset E)).filter (fun D => e ∈ D)).filter
      (fun D => D.card = q) =
      Finset.univ.filter (fun D => D.card = q ∧ e ∈ D) := by
    ext D
    simp [and_comm]
  rw [hfilter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_fixed_containing (E := E) e q hq0]
  have hm0 : 0 < Fintype.card E := lt_of_lt_of_le hq0 hqlt.le
  have hchoose : 0 < Nat.choose (Fintype.card E) q := Nat.choose_pos hqlt.le
  have hid := Nat.succ_mul_choose_eq (Fintype.card E - 1) (q - 1)
  have hm : Fintype.card E - 1 + 1 = Fintype.card E := Nat.sub_add_cancel hm0
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel hq0
  have hid' : Fintype.card E * Nat.choose (Fintype.card E - 1) (q - 1) =
      Nat.choose (Fintype.card E) q * q := by
    simpa [Nat.succ_eq_add_one, hm, hq] using hid
  have hidR : (Fintype.card E : ℝ) *
      (Nat.choose (Fintype.card E - 1) (q - 1) : ℝ) =
      (Nat.choose (Fintype.card E) q : ℝ) * q := by
    exact_mod_cast hid'
  field_simp [show (Fintype.card E : ℝ) ≠ 0 by positivity,
    show (Nat.choose (Fintype.card E) q : ℝ) ≠ 0 by positivity]
  nlinarith [hidR]

private noncomputable def binomialWeight (m q k : ℕ) : ℝ :=
  (Nat.choose m k : ℝ) * ((q : ℝ) / m) ^ k *
    (((m - q : ℕ) : ℝ) / m) ^ (m - k)

private theorem binomialWeight_succ_ge {m q k : ℕ}
    (hm0 : 0 < m) (hkq : k < q) (hqm : q ≤ m) :
    binomialWeight m q k ≤ binomialWeight m q (k + 1) := by
  have hkm : k < m := hkq.trans_le hqm
  have hcoeffN : Nat.choose m k * (m - q) ≤ Nat.choose m (k + 1) * q := by
    calc
      Nat.choose m k * (m - q) ≤ Nat.choose m k * (m - k) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hkq.le m)
      _ = Nat.choose m (k + 1) * (k + 1) :=
        (Nat.choose_succ_right_eq m k).symm
      _ ≤ Nat.choose m (k + 1) * q :=
        Nat.mul_le_mul_left _ hkq
  have hcoeffN' : (Nat.choose m k : ℝ) * ((m - q : ℕ) : ℝ) ≤
      (Nat.choose m (k + 1) : ℝ) * (q : ℝ) := by
    exact_mod_cast hcoeffN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hcoeff : (Nat.choose m k : ℝ) *
      (((m - q : ℕ) : ℝ) / m) ≤
      (Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m) := by
    calc
      (Nat.choose m k : ℝ) * (((m - q : ℕ) : ℝ) / m) =
          ((Nat.choose m k : ℝ) * ((m - q : ℕ) : ℝ)) / m := by ring
      _ ≤ ((Nat.choose m (k + 1) : ℝ) * (q : ℝ)) / m :=
        (div_le_div_right hmR).2 hcoeffN'
      _ = (Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m) := by ring
  have hp0 : 0 ≤ (q : ℝ) / m := by positivity
  have hr0 : 0 ≤ ((m - q : ℕ) : ℝ) / m := by positivity
  have hexp : m - k = (m - (k + 1)) + 1 := by omega
  unfold binomialWeight
  rw [hexp, pow_succ, pow_succ]
  have hcommon : 0 ≤ ((q : ℝ) / m) ^ k *
      (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hr0 _)
  have hmul := mul_le_mul_of_nonneg_left hcoeff hcommon
  calc
    (Nat.choose m k : ℝ) * ((q : ℝ) / m) ^ k *
        ((((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) *
          (((m - q : ℕ) : ℝ) / m)) =
      (((q : ℝ) / m) ^ k *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1))) *
        ((Nat.choose m k : ℝ) * (((m - q : ℕ) : ℝ) / m)) := by ring
    _ ≤ (((q : ℝ) / m) ^ k *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1))) *
        ((Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m)) := hmul
    _ = (Nat.choose m (k + 1) : ℝ) *
        (((q : ℝ) / m) ^ k * ((q : ℝ) / m)) *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) := by ring

private theorem binomialWeight_succ_le {m q k : ℕ}
    (hm0 : 0 < m) (hqk : q ≤ k) (hkm : k < m) :
    binomialWeight m q (k + 1) ≤ binomialWeight m q k := by
  have hcoeffN : Nat.choose m (k + 1) * q ≤ Nat.choose m k * (m - q) := by
    calc
      Nat.choose m (k + 1) * q ≤ Nat.choose m (k + 1) * (k + 1) :=
        Nat.mul_le_mul_left _ (hqk.trans (Nat.le_succ k))
      _ = Nat.choose m k * (m - k) := Nat.choose_succ_right_eq m k
      _ ≤ Nat.choose m k * (m - q) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hqk m)
  have hcoeffN' : (Nat.choose m (k + 1) : ℝ) * (q : ℝ) ≤
      (Nat.choose m k : ℝ) * ((m - q : ℕ) : ℝ) := by
    exact_mod_cast hcoeffN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hcoeff : (Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m) ≤
      (Nat.choose m k : ℝ) * (((m - q : ℕ) : ℝ) / m) := by
    calc
      (Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m) =
          ((Nat.choose m (k + 1) : ℝ) * (q : ℝ)) / m := by ring
      _ ≤ ((Nat.choose m k : ℝ) * ((m - q : ℕ) : ℝ)) / m :=
        (div_le_div_right hmR).2 hcoeffN'
      _ = (Nat.choose m k : ℝ) * (((m - q : ℕ) : ℝ) / m) := by ring
  have hp0 : 0 ≤ (q : ℝ) / m := by positivity
  have hr0 : 0 ≤ ((m - q : ℕ) : ℝ) / m := by positivity
  have hexp : m - k = (m - (k + 1)) + 1 := by omega
  unfold binomialWeight
  rw [hexp, pow_succ, pow_succ]
  have hcommon : 0 ≤ ((q : ℝ) / m) ^ k *
      (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hr0 _)
  have hmul := mul_le_mul_of_nonneg_left hcoeff hcommon
  calc
    (Nat.choose m (k + 1) : ℝ) *
        (((q : ℝ) / m) ^ k * ((q : ℝ) / m)) *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) =
      (((q : ℝ) / m) ^ k *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1))) *
        ((Nat.choose m (k + 1) : ℝ) * ((q : ℝ) / m)) := by ring
    _ ≤ (((q : ℝ) / m) ^ k *
          (((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1))) *
        ((Nat.choose m k : ℝ) * (((m - q : ℕ) : ℝ) / m)) := hmul
    _ = (Nat.choose m k : ℝ) * ((q : ℝ) / m) ^ k *
        ((((m - q : ℕ) : ℝ) / m) ^ (m - (k + 1)) *
          (((m - q : ℕ) : ℝ) / m)) := by ring

private theorem binomialWeight_le_mode {m q k : ℕ}
    (hm0 : 0 < m) (hqm : q ≤ m) (hkm : k ≤ m) :
    binomialWeight m q k ≤ binomialWeight m q q := by
  have hright : ∀ n, q ≤ n → n ≤ m →
      binomialWeight m q n ≤ binomialWeight m q q := by
    intro n hqn hnm
    induction n, hqn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hqn ih =>
        exact (binomialWeight_succ_le hm0 hqn
          (Nat.lt_of_succ_le hnm)).trans (ih ((Nat.le_succ n).trans hnm))
  by_cases hkq : k ≤ q
  · exact Nat.decreasingInduction'
      (fun n hn _ ih => (binomialWeight_succ_ge hm0 hn hqm).trans ih)
      hkq le_rfl
  · have hqk : q ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkq)
    exact hright k hqk hkm

theorem fixedCard_totalCorrelation_le_log_succ (m q : ℕ)
    (hq0 : 0 < q) (hqm : q < m) :
    (m : ℝ) * FiniteDist.binaryEntropy ((q : ℝ) / m) -
        Real.log (Nat.choose m q) ≤ Real.log (m + 1) := by
  have hm0 : 0 < m := hq0.trans hqm
  have hqle : q ≤ m := hqm.le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hp : 0 < (q : ℝ) / m := div_pos (by exact_mod_cast hq0) hmR
  have hr : 0 < ((m - q : ℕ) : ℝ) / m := by
    exact div_pos (by exact_mod_cast Nat.sub_pos_of_lt hqm) hmR
  have hchoose : 0 < (Nat.choose m q : ℝ) := by
    exact_mod_cast Nat.choose_pos hqle
  have hsum : ∑ k in Finset.range (m + 1), binomialWeight m q k = 1 := by
    have hadd : (q : ℝ) / m + ((m - q : ℕ) : ℝ) / m = 1 := by
      rw [Nat.cast_sub hqle]
      field_simp
    calc
      ∑ k in Finset.range (m + 1), binomialWeight m q k =
          (((q : ℝ) / m) + (((m - q : ℕ) : ℝ) / m)) ^ m := by
        rw [(Commute.all ((q : ℝ) / m)
          (((m - q : ℕ) : ℝ) / m)).add_pow]
        apply Finset.sum_congr rfl
        intro k _
        unfold binomialWeight
        ring
      _ = 1 := by rw [hadd, one_pow]
  have hsumle : 1 ≤ (m + 1 : ℝ) * binomialWeight m q q := by
    calc
      1 = ∑ k in Finset.range (m + 1), binomialWeight m q k := hsum.symm
      _ ≤
          ∑ _k in Finset.range (m + 1), binomialWeight m q q := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < m + 1 := Finset.mem_range.mp hk
        exact binomialWeight_le_mode hm0 hqle (by omega)
      _ = (m + 1 : ℝ) * binomialWeight m q q := by simp
  have hwpos : 0 < binomialWeight m q q := by
    unfold binomialWeight
    positivity
  have hlognonneg : 0 ≤ Real.log ((m + 1 : ℝ) * binomialWeight m q q) := by
    have hlog := Real.log_le_log (by norm_num) hsumle
    simpa using hlog
  have hlogsplit : Real.log ((m + 1 : ℝ) * binomialWeight m q q) =
      Real.log (m + 1) + Real.log (binomialWeight m q q) := by
    rw [Real.log_mul (by positivity) hwpos.ne']
  rw [hlogsplit] at hlognonneg
  have hlogweight : Real.log (binomialWeight m q q) =
      Real.log (Nat.choose m q) +
        (q : ℝ) * Real.log ((q : ℝ) / m) +
        ((m - q : ℕ) : ℝ) *
          Real.log (((m - q : ℕ) : ℝ) / m) := by
    unfold binomialWeight
    rw [show (Nat.choose m q : ℝ) * ((q : ℝ) / m) ^ q *
        (((m - q : ℕ) : ℝ) / m) ^ (m - q) =
      (Nat.choose m q : ℝ) *
        (((q : ℝ) / m) ^ q *
          (((m - q : ℕ) : ℝ) / m) ^ (m - q)) by ring]
    rw [Real.log_mul hchoose.ne' (mul_ne_zero (pow_ne_zero _ hp.ne')
      (pow_ne_zero _ hr.ne')), Real.log_mul (pow_ne_zero _ hp.ne')
        (pow_ne_zero _ hr.ne'), Real.log_pow, Real.log_pow]
    ring
  have hmp : (m : ℝ) * ((q : ℝ) / m) = q := by field_simp
  have hmone : (m : ℝ) * (1 - (q : ℝ) / m) = (m - q : ℕ) := by
    rw [Nat.cast_sub hqle]
    field_simp
  have hr_eq : 1 - (q : ℝ) / m = ((m - q : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hqle]
    field_simp
  have hcorr :
      (m : ℝ) * FiniteDist.binaryEntropy ((q : ℝ) / m) -
          Real.log (Nat.choose m q) = -Real.log (binomialWeight m q q) := by
    unfold FiniteDist.binaryEntropy Real.negMulLog
    calc
      (m : ℝ) *
            (-((q : ℝ) / m) * Real.log ((q : ℝ) / m) +
              (-(1 - (q : ℝ) / m) * Real.log (1 - (q : ℝ) / m))) -
          Real.log (Nat.choose m q) =
        -((m : ℝ) * ((q : ℝ) / m)) * Real.log ((q : ℝ) / m) -
          ((m : ℝ) * (1 - (q : ℝ) / m)) *
            Real.log (1 - (q : ℝ) / m) - Real.log (Nat.choose m q) := by ring
      _ = -(q : ℝ) * Real.log ((q : ℝ) / m) -
          ((m - q : ℕ) : ℝ) *
            Real.log (((m - q : ℕ) : ℝ) / m) -
          Real.log (Nat.choose m q) := by rw [hmp, hmone, hr_eq]
      _ = -Real.log (binomialWeight m q q) := by rw [hlogweight]; ring
  rw [hcorr]
  linarith

theorem fixedCard_expectedBelong_le_bits
    [Nonempty M] (Φ : Scheme E M) (s q : ℕ) (hq0 : 0 < q)
    (hqlt : q < Fintype.card E) (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s) :
    expectedBelong (fixedCardDist (E := E) q hqlt.le) Φ
        ((q : ℝ) / Fintype.card E) ≤
      (20 / ((q : ℝ) / Fintype.card E)) *
        ((s : ℝ) * Real.log 2 +
          ((Fintype.card E : ℝ) *
            FiniteDist.binaryEntropy ((q : ℝ) / Fintype.card E) -
              Real.log (Nat.choose (Fintype.card E) q))) := by
  have hm0 : 0 < Fintype.card E := lt_of_lt_of_le hq0 hqlt.le
  have hδ0 : 0 < (q : ℝ) / Fintype.card E :=
    div_pos (by exact_mod_cast hq0) (by exact_mod_cast hm0)
  have hδhalf : (q : ℝ) / Fintype.card E ≤ 1 / 2 := by
    apply (div_le_iff (by exact_mod_cast hm0)).2
    have hc : (2 * q : ℕ) ≤ Fintype.card E := hqhalf
    have hcR : (2 * q : ℝ) ≤ Fintype.card E := by exact_mod_cast hc
    norm_num at hcR ⊢
    linarith
  have h := expectedBelong_le_bits (fixedCardDist (E := E) q hqlt.le) Φ s
    hδ0 hδhalf (fun e => fixedCardDist_marginal e q hq0 hqlt) hcard
  simpa [fixedCardDist_entropy] using h

theorem fixedCard_expectedBelong_le_bits_log_succ
    [Nonempty M] (Φ : Scheme E M) (s q : ℕ) (hq0 : 0 < q)
    (hqlt : q < Fintype.card E) (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s) :
    expectedBelong (fixedCardDist (E := E) q hqlt.le) Φ
        ((q : ℝ) / Fintype.card E) ≤
      (20 / ((q : ℝ) / Fintype.card E)) *
        ((s : ℝ) * Real.log 2 + Real.log (Fintype.card E + 1)) := by
  have h := fixedCard_expectedBelong_le_bits Φ s q hq0 hqlt hqhalf hcard
  have hcorr := fixedCard_totalCorrelation_le_log_succ
    (Fintype.card E) q hq0 hqlt
  apply h.trans
  apply mul_le_mul_of_nonneg_left (by linarith)
  have hm0 : 0 < Fintype.card E := hq0.trans hqlt
  positivity

theorem fixedCard_expectedBelong_le_forty_of_correlation
    [Nonempty M] (Φ : Scheme E M) (s q : ℕ) (hq0 : 0 < q)
    (hqlt : q < Fintype.card E) (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s)
    (hcorr : (Fintype.card E : ℝ) *
        FiniteDist.binaryEntropy ((q : ℝ) / Fintype.card E) -
          Real.log (Nat.choose (Fintype.card E) q) ≤ (s : ℝ) * Real.log 2) :
    expectedBelong (fixedCardDist (E := E) q hqlt.le) Φ
        ((q : ℝ) / Fintype.card E) ≤
      40 * (s : ℝ) * Real.log 2 / ((q : ℝ) / Fintype.card E) := by
  have h := fixedCard_expectedBelong_le_bits Φ s q hq0 hqlt hqhalf hcard
  have hm0 : 0 < Fintype.card E := lt_of_lt_of_le hq0 hqlt.le
  have hδ0 : 0 < (q : ℝ) / Fintype.card E :=
    div_pos (by exact_mod_cast hq0) (by exact_mod_cast hm0)
  calc
    expectedBelong (fixedCardDist (E := E) q hqlt.le) Φ
        ((q : ℝ) / Fintype.card E)
      ≤ (20 / ((q : ℝ) / Fintype.card E)) *
          (2 * ((s : ℝ) * Real.log 2)) := by
        apply h.trans
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
    _ = 40 * (s : ℝ) * Real.log 2 / ((q : ℝ) / Fintype.card E) := by
      field_simp [hδ0.ne']
      ring

theorem fixedCard_expectedBelong_le_forty
    [Nonempty M] (Φ : Scheme E M) (s q : ℕ) (hq0 : 0 < q)
    (hqlt : q < Fintype.card E) (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s)
    (hbudget : Real.log (Fintype.card E + 1) ≤ (s : ℝ) * Real.log 2) :
    expectedBelong (fixedCardDist (E := E) q hqlt.le) Φ
        ((q : ℝ) / Fintype.card E) ≤
      40 * (s : ℝ) * Real.log 2 / ((q : ℝ) / Fintype.card E) := by
  apply fixedCard_expectedBelong_le_forty_of_correlation Φ s q hq0 hqlt
    hqhalf hcard
  exact (fixedCard_totalCorrelation_le_log_succ
    (Fintype.card E) q hq0 hqlt).trans hbudget

end FixedCard

def projectionSupport (E : Type*) [Fintype E] [DecidableEq E]
    (q : ℕ) (B : Finset E) : Finset (Finset E) :=
  ((Finset.univ : Finset E).powersetCard q).image (fun D => D \ B)

theorem appendixA_projection_support_counterexample :
    Nat.choose 2 1 <
      (projectionSupport (Fin 3) 1 ({0} : Finset (Fin 3))).card := by
  native_decide

end Compression

end Formal.Streaming
