import SemiStreamingMatching.Proofs.Framework.DeletionParameters
import SemiStreamingMatching.Proofs.Framework.FiniteConcentration
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Formal.Streaming

namespace FixedCard

variable {E : Type*} [Fintype E] [DecidableEq E]

def selectedPairs (A D : Finset E) : Finset (E × E) :=
  (A ∩ D).offDiag

theorem selectedPairs_card (A D : Finset E) :
    (selectedPairs A D).card =
      (A ∩ D).card * ((A ∩ D).card - 1) := by
  rw [selectedPairs, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib]
  simp

private theorem card_finsets_containing_pair (x y : E) (hxy : x ≠ y)
    (q : ℕ) (hq : 2 ≤ q) :
    ((Finset.univ : Finset (Finset E)).filter
      (fun D ↦ D.card = q ∧ x ∈ D ∧ y ∈ D)).card =
      Nat.choose (Fintype.card E - 2) (q - 2) := by
  classical
  let source := (((Finset.univ : Finset E).erase x).erase y).powersetCard (q - 2)
  let addPair : Finset E → Finset E := fun S ↦ insert x (insert y S)
  have himage :
      ((Finset.univ : Finset (Finset E)).filter
        (fun D ↦ D.card = q ∧ x ∈ D ∧ y ∈ D)) =
        source.image addPair := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_powersetCard, source, addPair]
    constructor
    · rintro ⟨hcard, hxD, hyD⟩
      refine ⟨(D.erase x).erase y, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨(Finset.mem_erase.1 hz).1,
            (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).1⟩
        · rw [Finset.card_erase_of_mem]
          · rw [Finset.card_erase_of_mem hxD, hcard]
            omega
          · simpa [hxy.symm] using hyD
      · have hyEraseX : y ∈ D.erase x := by simpa [hxy.symm] using hyD
        rw [Finset.insert_erase hyEraseX]
        rw [Finset.insert_erase hxD]
    · rintro ⟨S, hS, rfl⟩
      have hxS : x ∉ S := by
        intro hx
        have hx' := hS.1 hx
        simp [hxy] at hx'
      have hyS : y ∉ S := by
        intro hy
        have hy' := hS.1 hy
        simp at hy'
      refine ⟨?_, Finset.mem_insert_self _ _, by simp⟩
      rw [Finset.card_insert_of_not_mem (by simpa [hxy, hxS, hyS]),
        Finset.card_insert_of_not_mem hyS, hS.2]
      omega
  rw [himage]
  have hinj : Set.InjOn addPair (↑source : Set (Finset E)) := by
    intro S hS T hT hST
    have hSp : S ⊆ ((Finset.univ : Finset E).erase x).erase y ∧
        S.card = q - 2 := by simpa [source] using hS
    have hTp : T ⊆ ((Finset.univ : Finset E).erase x).erase y ∧
        T.card = q - 2 := by simpa [source] using hT
    have hxS : x ∉ S := by
      intro hx
      have hx' := hSp.1 hx
      simp [hxy] at hx'
    have hyS : y ∉ S := by
      intro hy
      have hy' := hSp.1 hy
      simp at hy'
    have hxT : x ∉ T := by
      intro hx
      have hx' := hTp.1 hx
      simp [hxy] at hx'
    have hyT : y ∉ T := by
      intro hy
      have hy' := hTp.1 hy
      simp at hy'
    have hrecoverS : ((addPair S).erase x).erase y = S := by
      simp [addPair, hxy, hxy.symm, hxS, hyS]
    have hrecoverT : ((addPair T).erase x).erase y = T := by
      simp [addPair, hxy, hxy.symm, hxT, hyT]
    rw [← hrecoverS, hST, hrecoverT]
  rw [Finset.card_image_iff.mpr hinj, Finset.card_powersetCard]
  congr 1
  have hyErase : y ∈ (Finset.univ : Finset E).erase x := by simp [hxy.symm]
  rw [Finset.card_erase_of_mem hyErase,
    Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp
  omega

private def containingPairEquiv (x y : E) (q : ℕ) :
    {D : FixedCard E q // x ∈ D.1 ∧ y ∈ D.1} ≃
      {D : Finset E // D.card = q ∧ x ∈ D ∧ y ∈ D} where
  toFun D := ⟨D.1.1, D.1.2, D.2.1, D.2.2⟩
  invFun D := ⟨⟨D.1, D.2.1⟩, D.2.2.1, D.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_fixedCard_containing_pair (x y : E) (hxy : x ≠ y)
    (q : ℕ) (hq : 2 ≤ q) :
    ((Finset.univ : Finset (FixedCard E q)).filter
      (fun D ↦ x ∈ D.1 ∧ y ∈ D.1)).card =
      Nat.choose (Fintype.card E - 2) (q - 2) := by
  calc
    ((Finset.univ : Finset (FixedCard E q)).filter
        (fun D ↦ x ∈ D.1 ∧ y ∈ D.1)).card =
        Fintype.card {D : FixedCard E q // x ∈ D.1 ∧ y ∈ D.1} := by
      simpa using (Fintype.card_coe
        ((Finset.univ : Finset (FixedCard E q)).filter
          (fun D ↦ x ∈ D.1 ∧ y ∈ D.1))).symm
    _ = Fintype.card
        {D : Finset E // D.card = q ∧ x ∈ D ∧ y ∈ D} :=
      Fintype.card_congr (containingPairEquiv x y q)
    _ = ((Finset.univ : Finset (Finset E)).filter
        (fun D ↦ D.card = q ∧ x ∈ D ∧ y ∈ D)).card := by
      simpa using (Fintype.card_coe
        ((Finset.univ : Finset (Finset E)).filter
          (fun D ↦ D.card = q ∧ x ∈ D ∧ y ∈ D)))
    _ = Nat.choose (Fintype.card E - 2) (q - 2) :=
      card_finsets_containing_pair x y hxy q hq

theorem sum_inter_card_mul_pred (A : Finset E) (q : ℕ) (hq : 2 ≤ q) :
    (∑ D : FixedCard E q,
      (A ∩ D.1).card * ((A ∩ D.1).card - 1)) =
      (A.card * (A.card - 1)) *
        Nat.choose (Fintype.card E - 2) (q - 2) := by
  classical
  have hselected (D : FixedCard E q) :
      selectedPairs A D.1 = A.offDiag.filter
        (fun z ↦ z.1 ∈ D.1 ∧ z.2 ∈ D.1) := by
    ext z
    simp only [selectedPairs, Finset.mem_offDiag, Finset.mem_inter,
      Finset.mem_filter]
    aesop
  calc
    (∑ D : FixedCard E q,
      (A ∩ D.1).card * ((A ∩ D.1).card - 1)) =
        ∑ D : FixedCard E q, (selectedPairs A D.1).card := by
      apply Finset.sum_congr rfl
      intro D _hD
      exact (selectedPairs_card A D.1).symm
    _ = ∑ D : FixedCard E q,
        ∑ z in A.offDiag, if z.1 ∈ D.1 ∧ z.2 ∈ D.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro D _hD
      rw [hselected D, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ z in A.offDiag,
        ∑ D : FixedCard E q, if z.1 ∈ D.1 ∧ z.2 ∈ D.1 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _z in A.offDiag,
        Nat.choose (Fintype.card E - 2) (q - 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← card_fixedCard_containing_pair z.1 z.2
        (Finset.mem_offDiag.1 hz).2.2 q hq]
      simp
    _ = (A.card * (A.card - 1)) *
        Nat.choose (Fintype.card E - 2) (q - 2) := by
      rw [Finset.sum_const, Finset.offDiag_card]
      simp only [nsmul_eq_mul]
      congr 1
      rw [Nat.mul_sub_left_distrib]
      simp

theorem card_mul_pred_mul_choose_sub_two (q : ℕ)
    (hq : 2 ≤ q) (hqn : q ≤ Fintype.card E) :
    Fintype.card E * (Fintype.card E - 1) *
        Nat.choose (Fintype.card E - 2) (q - 2) =
      q * (q - 1) * Nat.choose (Fintype.card E) q := by
  let n := Fintype.card E
  have hn2 : 2 ≤ n := hq.trans hqn
  have hnstep : n - 2 + 1 = n - 1 := by omega
  have hqstep : q - 2 + 1 = q - 1 := by omega
  have hnlast : n - 1 + 1 = n := by omega
  have hqlast : q - 1 + 1 = q := by omega
  have hfirst := Nat.succ_mul_choose_eq (n - 2) (q - 2)
  have hsecond := Nat.succ_mul_choose_eq (n - 1) (q - 1)
  have hfirst' : (n - 1) * Nat.choose (n - 2) (q - 2) =
      Nat.choose (n - 1) (q - 1) * (q - 1) := by
    simpa [Nat.succ_eq_add_one, hnstep, hqstep] using hfirst
  have hsecond' : n * Nat.choose (n - 1) (q - 1) =
      Nat.choose n q * q := by
    simpa [Nat.succ_eq_add_one, hnlast, hqlast] using hsecond
  change n * (n - 1) * Nat.choose (n - 2) (q - 2) =
    q * (q - 1) * Nat.choose n q
  calc
    n * (n - 1) * Nat.choose (n - 2) (q - 2) =
        n * ((n - 1) * Nat.choose (n - 2) (q - 2)) := by ring
    _ = n * (Nat.choose (n - 1) (q - 1) * (q - 1)) := by rw [hfirst']
    _ = (n * Nat.choose (n - 1) (q - 1)) * (q - 1) := by ring
    _ = (Nat.choose n q * q) * (q - 1) := by rw [hsecond']
    _ = q * (q - 1) * Nat.choose n q := by ring

def intersectionMean (A : Finset E) (q : ℕ) : ℚ :=
  (q : ℚ) * A.card / Fintype.card E

theorem intersectionMean_nonneg (A : Finset E) (q : ℕ) :
    0 ≤ intersectionMean A q := by
  unfold intersectionMean
  positivity

theorem sum_inter_card_eq_mean_mul_card (A : Finset E) (q : ℕ)
    (hq : q ≤ Fintype.card E) :
    (∑ D : FixedCard E q, ((A ∩ D.1).card : ℚ)) =
      intersectionMean A q * Fintype.card (FixedCard E q) := by
  by_cases hn : Fintype.card E = 0
  · have hq0 : q = 0 := Nat.eq_zero_of_le_zero (hn ▸ hq)
    subst q
    letI : IsEmpty E := Fintype.card_eq_zero_iff.mp hn
    have hA : A = ∅ := by
      ext e
      exact isEmptyElim e
    subst A
    simp [intersectionMean, hn]
  · have hnQ : (Fintype.card E : ℚ) ≠ 0 := by exact_mod_cast hn
    have hexact := card_mul_sum_inter_card A q hq
    have hexactQ :
        (Fintype.card E : ℚ) *
            ∑ D : FixedCard E q, ((A ∩ D.1).card : ℚ) =
          (q : ℚ) * A.card * Fintype.card (FixedCard E q) := by
      exact_mod_cast hexact
    apply (mul_left_cancel₀ hnQ)
    calc
      (Fintype.card E : ℚ) *
          (∑ D : FixedCard E q, ((A ∩ D.1).card : ℚ)) =
          (q : ℚ) * A.card * Fintype.card (FixedCard E q) := hexactQ
      _ = (Fintype.card E : ℚ) *
          (intersectionMean A q * Fintype.card (FixedCard E q)) := by
        unfold intersectionMean
        field_simp
        <;> ring

theorem card_mul_pred_mul_sum_inter_card_mul_pred
    (A : Finset E) (q : ℕ) (hq2 : 2 ≤ q)
    (hqn : q ≤ Fintype.card E) :
    (Fintype.card E : ℚ) * ((Fintype.card E - 1 : ℕ) : ℚ) *
        (∑ D : FixedCard E q,
          (((A ∩ D.1).card * ((A ∩ D.1).card - 1) : ℕ) : ℚ)) =
      (A.card : ℚ) * ((A.card - 1 : ℕ) : ℚ) * (q : ℚ) *
        ((q - 1 : ℕ) : ℚ) *
        Fintype.card (FixedCard E q) := by
  have hsum := sum_inter_card_mul_pred A q hq2
  have hchoose := card_mul_pred_mul_choose_sub_two (E := E) q hq2 hqn
  have hnat :
      Fintype.card E * (Fintype.card E - 1) *
          (∑ D : FixedCard E q,
            (A ∩ D.1).card * ((A ∩ D.1).card - 1)) =
        A.card * (A.card - 1) * q * (q - 1) *
          Fintype.card (FixedCard E q) := by
    rw [hsum, FixedCard.card]
    calc
      Fintype.card E * (Fintype.card E - 1) *
          (A.card * (A.card - 1) *
            Nat.choose (Fintype.card E - 2) (q - 2)) =
          (A.card * (A.card - 1)) *
            (Fintype.card E * (Fintype.card E - 1) *
              Nat.choose (Fintype.card E - 2) (q - 2)) := by ring
      _ = (A.card * (A.card - 1)) *
          (q * (q - 1) * Nat.choose (Fintype.card E) q) := by rw [hchoose]
      _ = A.card * (A.card - 1) * q * (q - 1) *
          Nat.choose (Fintype.card E) q := by ring
  exact_mod_cast hnat

theorem sum_inter_card_mul_pred_le_mean_sq_mul_card
    (A : Finset E) (q : ℕ) (hq : q ≤ Fintype.card E) :
    (∑ D : FixedCard E q,
      (((A ∩ D.1).card * ((A ∩ D.1).card - 1) : ℕ) : ℚ)) ≤
      (intersectionMean A q) ^ 2 * Fintype.card (FixedCard E q) := by
  by_cases hq2 : 2 ≤ q
  · let n := Fintype.card E
    let a := A.card
    let c := Fintype.card (FixedCard E q)
    have hn2 : 2 ≤ n := hq2.trans hq
    have ha : a ≤ n := by
      exact Finset.card_le_card (Finset.subset_univ A)
    have hnpos : (0 : ℚ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn2)
    have hnpredpos : (0 : ℚ) < (n - 1 : ℕ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    have hdenpos : (0 : ℚ) < (n : ℚ) * ((n - 1 : ℕ) : ℚ) :=
      mul_pos hnpos hnpredpos
    have hcross :=
      card_mul_pred_mul_sum_inter_card_mul_pred A q hq2 hq
    change (n : ℚ) * ((n - 1 : ℕ) : ℚ) *
        (∑ D : FixedCard E q,
          (((A ∩ D.1).card * ((A ∩ D.1).card - 1) : ℕ) : ℚ)) =
      (a : ℚ) * ((a - 1 : ℕ) : ℚ) * (q : ℚ) *
        ((q - 1 : ℕ) : ℚ) * c at hcross
    have hnqRatio : n * (q - 1) ≤ q * (n - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      simp only [mul_one]
      rw [mul_comm q n]
      exact Nat.sub_le_sub_left hq (n * q)
    have hpolyNat :
        n * a * (a - 1) * q * (q - 1) * c ≤
          (n - 1) * q * q * a * a * c := by
      calc
        n * a * (a - 1) * q * (q - 1) * c =
            (a * (a - 1) * q) * (n * (q - 1)) * c := by ring
        _ ≤ (a * (a - 1) * q) * (q * (n - 1)) * c := by
          gcongr
        _ ≤ (a * a * q) * (q * (n - 1)) * c := by
          gcongr
          omega
        _ = (n - 1) * q * q * a * a * c := by ring
    have hpolyQ :
        (n : ℚ) * (a : ℚ) * ((a - 1 : ℕ) : ℚ) * (q : ℚ) *
              ((q - 1 : ℕ) : ℚ) * c ≤
          ((n - 1 : ℕ) : ℚ) * (q : ℚ) * q * a * a * c := by
      exact_mod_cast hpolyNat
    have htarget :
        (a : ℚ) * ((a - 1 : ℕ) : ℚ) * (q : ℚ) *
            ((q - 1 : ℕ) : ℚ) * c ≤
          (n : ℚ) * ((n - 1 : ℕ) : ℚ) *
            (intersectionMean A q ^ 2 * c) := by
      apply (le_of_mul_le_mul_left ?_ hnpos)
      calc
        (n : ℚ) *
            ((a : ℚ) * ((a - 1 : ℕ) : ℚ) * (q : ℚ) *
              ((q - 1 : ℕ) : ℚ) * c) ≤
            ((n - 1 : ℕ) : ℚ) * (q : ℚ) * q * a * a * c :=
          by simpa only [mul_assoc] using hpolyQ
        _ = (n : ℚ) *
            ((n : ℚ) * ((n - 1 : ℕ) : ℚ) *
              (intersectionMean A q ^ 2 * c)) := by
          dsimp [intersectionMean, n, a, c]
          field_simp
          <;> ring
    apply (le_of_mul_le_mul_left ?_ hdenpos)
    rw [hcross]
    exact htarget
  · have hq1 : q ≤ 1 := by omega
    have hzero : ∀ D : FixedCard E q,
        (A ∩ D.1).card * ((A ∩ D.1).card - 1) = 0 := by
      intro D
      have hinter : (A ∩ D.1).card ≤ q := by
        exact (Finset.card_le_card (Finset.inter_subset_right A D.1)).trans_eq D.2
      have hx : (A ∩ D.1).card = 0 ∨ (A ∩ D.1).card = 1 := by omega
      rcases hx with hx | hx <;> simp [hx]
    simp_rw [hzero]
    simp only [Nat.cast_zero, Finset.sum_const_zero]
    positivity

theorem sum_sq_sub_intersectionMean_le
    (A : Finset E) (q : ℕ) (hq : q ≤ Fintype.card E) :
    (∑ D : FixedCard E q,
      (((A ∩ D.1).card : ℚ) - intersectionMean A q) ^ 2) ≤
      intersectionMean A q * Fintype.card (FixedCard E q) := by
  let X : FixedCard E q → ℚ := fun D ↦ ((A ∩ D.1).card : ℚ)
  let mu := intersectionMean A q
  let cardOmega : ℚ := Fintype.card (FixedCard E q)
  have hmean : (∑ D : FixedCard E q, X D) = mu * cardOmega := by
    exact sum_inter_card_eq_mean_mul_card A q hq
  have hfall : (∑ D : FixedCard E q, X D * (X D - 1)) ≤
      mu ^ 2 * cardOmega := by
    have h := sum_inter_card_mul_pred_le_mean_sq_mul_card A q hq
    have hterm (D : FixedCard E q) :
        X D * (X D - 1) =
          (((A ∩ D.1).card * ((A ∩ D.1).card - 1) : ℕ) : ℚ) := by
      dsimp only [X]
      generalize (A ∩ D.1).card = k
      cases k with
      | zero => simp
      | succ k =>
          push_cast
          ring
    calc
      (∑ D : FixedCard E q, X D * (X D - 1)) =
          ∑ D : FixedCard E q,
            (((A ∩ D.1).card * ((A ∩ D.1).card - 1) : ℕ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro D _hD
        exact hterm D
      _ ≤ intersectionMean A q ^ 2 *
          Fintype.card (FixedCard E q) := h
      _ = mu ^ 2 * cardOmega := rfl
  have hpoint (D : FixedCard E q) :
      (X D - mu) ^ 2 =
        X D * (X D - 1) + X D - 2 * mu * X D + mu ^ 2 := by ring
  have hlinear :
      (∑ D : FixedCard E q, 2 * mu * X D) =
        2 * mu * (∑ D : FixedCard E q, X D) := by
    exact (Finset.mul_sum Finset.univ X (2 * mu)).symm
  have hconst :
      (∑ _D : FixedCard E q, mu ^ 2) = mu ^ 2 * cardOmega := by
    simp [cardOmega]
    ring
  calc
    (∑ D : FixedCard E q, (X D - mu) ^ 2) =
        ∑ D : FixedCard E q,
          (X D * (X D - 1) + X D - 2 * mu * X D + mu ^ 2) := by
      apply Finset.sum_congr rfl
      intro D _hD
      exact hpoint D
    _ =
        (∑ D : FixedCard E q, X D * (X D - 1)) +
          (∑ D : FixedCard E q, X D) -
          2 * mu * (∑ D : FixedCard E q, X D) +
          mu ^ 2 * cardOmega := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hlinear, hconst]
    _ ≤ mu ^ 2 * cardOmega + (mu * cardOmega) -
          2 * mu * (mu * cardOmega) + mu ^ 2 * cardOmega := by
      rw [hmean]
      gcongr
    _ = mu * cardOmega := by ring

end FixedCard

theorem sum_pi_apply_mul_apply_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (Y : I → Type*) [∀ i, Fintype (Y i)]
    (i j : I) (hij : i ≠ j) (g : ∀ i, Y i → ℚ)
    (hzero : ∑ y : Y i, g i y = 0) :
    (∑ y : (∀ k, Y k), g i (y i) * g j (y j)) = 0 := by
  let e := Equiv.piSplitAt i Y
  let j' : {k : I // k ≠ i} := ⟨j, hij.symm⟩
  calc
    (∑ y : (∀ k, Y k), g i (y i) * g j (y j)) =
        ∑ z : Y i × (∀ k : {k // k ≠ i}, Y k),
          g i z.1 * g j (z.2 j') := by
      apply Fintype.sum_equiv e
      intro y
      rfl
    _ = ∑ a : Y i, ∑ z : (∀ k : {k // k ≠ i}, Y k),
          g i a * g j (z j') := by
      rw [Fintype.sum_prod_type]
    _ = (∑ a : Y i, g i a) *
        (∑ z : (∀ k : {k // k ≠ i}, Y k), g j (z j')) := by
      rw [Finset.sum_mul_sum]
    _ = 0 := by rw [hzero, zero_mul]

theorem sum_pi_sum_sq_eq_sum_coordinate_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (Y : I → Type*) [∀ i, Fintype (Y i)]
    (g : ∀ i, Y i → ℚ)
    (hzero : ∀ i, ∑ y : Y i, g i y = 0) :
    (∑ y : (∀ k, Y k), (∑ i : I, g i (y i)) ^ 2) =
      ∑ i : I,
        (Fintype.card (∀ k : {k // k ≠ i}, Y k) : ℚ) *
          ∑ a : Y i, (g i a) ^ 2 := by
  have hsquare (y : ∀ k, Y k) :
      (∑ i : I, g i (y i)) ^ 2 =
        ∑ i : I, ∑ j : I, g i (y i) * g j (y j) := by
    rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ y : (∀ k, Y k), (∑ i : I, g i (y i)) ^ 2) =
        ∑ y : (∀ k, Y k),
          ∑ i : I, ∑ j : I, g i (y i) * g j (y j) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact hsquare y
    _ = ∑ i : I, ∑ j : I,
        ∑ y : (∀ k, Y k), g i (y i) * g j (y j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : I, ∑ y : (∀ k, Y k), (g i (y i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_eq_single i]
      · apply Finset.sum_congr rfl
        intro y _hy
        ring
      · intro j _hj hji
        simpa only [mul_comm] using
          (sum_pi_apply_mul_apply_eq_zero Y j i hji g (hzero j))
      · simp
    _ = ∑ i : I,
        (Fintype.card (∀ k : {k // k ≠ i}, Y k) : ℚ) *
          ∑ a : Y i, (g i a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact sum_pi_apply_eq_card_mul_sum Y i (fun a ↦ (g i a) ^ 2)

theorem sum_pi_sum_sq_le_of_coordinate_bounds
    {I : Type*} [Fintype I] [DecidableEq I]
    (Y : I → Type*) [∀ i, Fintype (Y i)]
    (g : ∀ i, Y i → ℚ) (variance : I → ℚ)
    (hzero : ∀ i, ∑ y : Y i, g i y = 0)
    (hvariance : ∀ i,
      (∑ y : Y i, (g i y) ^ 2) ≤ variance i * Fintype.card (Y i)) :
    (∑ y : (∀ k, Y k), (∑ i : I, g i (y i)) ^ 2) ≤
      (∑ i : I, variance i) * Fintype.card (∀ k, Y k) := by
  rw [sum_pi_sum_sq_eq_sum_coordinate_sq Y g hzero]
  calc
    (∑ i : I,
      (Fintype.card (∀ k : {k // k ≠ i}, Y k) : ℚ) *
        ∑ a : Y i, (g i a) ^ 2) ≤
        ∑ i : I,
          (Fintype.card (∀ k : {k // k ≠ i}, Y k) : ℚ) *
            (variance i * Fintype.card (Y i)) := by
      gcongr with i
      exact hvariance i
    _ = ∑ i : I, variance i * Fintype.card (∀ k, Y k) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [card_pi_eq_card_mul_card_compl Y i]
      push_cast
      ring
    _ = (∑ i : I, variance i) * Fintype.card (∀ k, Y k) := by
      rw [Finset.sum_mul]

namespace HardDistribution

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def canonicalDeletionCharge (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (D : DeletionProfile B H q J) : ℕ :=
  ∑ p : Fin B.P, (canonicalInPart B H J p ∩ (D p).1).card

noncomputable def playerCanonicalDeletionMean (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (p : Fin B.P) : ℚ :=
  FixedCard.intersectionMean (canonicalInPart B H J p) (q p)

noncomputable def conditionalCanonicalDeletionMean (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t) : ℚ :=
  ∑ p : Fin B.P, playerCanonicalDeletionMean B H q J p

theorem canonicalDeletionCount_le_charge
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (D : DeletionProfile B H q J) :
    canonicalDeletionCount (⟨J, D⟩ : Sample B H q) ≤
      canonicalDeletionCharge B H q J D := by
  have h := canonical_sdiff_kept_card_le_sum_inter_deletion
    B H q (⟨J, D⟩ : Sample B H q)
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro p _hp
  exact (canonicalInPart_inter_deletion_card B H J p (q p) (D p)).symm

theorem playerCanonicalDeletionMean_nonneg
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t) (p : Fin B.P) :
    0 ≤ playerCanonicalDeletionMean B H q J p :=
  FixedCard.intersectionMean_nonneg _ _

theorem conditionalCanonicalDeletionMean_nonneg
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t) :
    0 ≤ conditionalCanonicalDeletionMean B H q J := by
  exact Finset.sum_nonneg fun p _hp ↦
    playerCanonicalDeletionMean_nonneg B H q J p

theorem deletionProfile_sum_charge_eq_mean
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) :
    (∑ D : DeletionProfile B H q J,
      (canonicalDeletionCharge B H q J D : ℚ)) =
      conditionalCanonicalDeletionMean B H q J *
        Fintype.card (DeletionProfile B H q J) := by
  classical
  calc
    (∑ D : DeletionProfile B H q J,
      (canonicalDeletionCharge B H q J D : ℚ)) =
        ∑ p : Fin B.P, ∑ D : DeletionProfile B H q J,
          ((canonicalInPart B H J p ∩ (D p).1).card : ℚ) := by
      simp only [canonicalDeletionCharge, Nat.cast_sum]
      rw [Finset.sum_comm]
    _ = ∑ p : Fin B.P,
        (Fintype.card (∀ k : {k // k ≠ p},
            PlayerDeletion B H J k (q k)) : ℚ) *
          ∑ D : PlayerDeletion B H J p (q p),
            ((canonicalInPart B H J p ∩ D.1).card : ℚ) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact sum_pi_apply_eq_card_mul_sum
        (fun k ↦ PlayerDeletion B H J k (q k)) p
          (fun D ↦ ((canonicalInPart B H J p ∩ D.1).card : ℚ))
    _ = ∑ p : Fin B.P,
        playerCanonicalDeletionMean B H q J p *
          Fintype.card (DeletionProfile B H q J) := by
      apply Finset.sum_congr rfl
      intro p _hp
      have hqp : q p ≤ Fintype.card
          {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
        simpa only [Fintype.card_coe] using hq p
      rw [FixedCard.sum_inter_card_eq_mean_mul_card
        (canonicalInPart B H J p) (q p) hqp]
      rw [card_pi_eq_card_mul_card_compl
        (fun k ↦ PlayerDeletion B H J k (q k)) p]
      dsimp only [playerCanonicalDeletionMean]
      push_cast
      ring
    _ = conditionalCanonicalDeletionMean B H q J *
        Fintype.card (DeletionProfile B H q J) := by
      rw [← Finset.sum_mul]
      rfl

theorem deletionProfile_sum_sq_charge_sub_mean_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) :
    (∑ D : DeletionProfile B H q J,
      ((canonicalDeletionCharge B H q J D : ℚ) -
        conditionalCanonicalDeletionMean B H q J) ^ 2) ≤
      conditionalCanonicalDeletionMean B H q J *
        Fintype.card (DeletionProfile B H q J) := by
  classical
  let Y := fun p : Fin B.P ↦ PlayerDeletion B H J p (q p)
  let mu := fun p : Fin B.P ↦ playerCanonicalDeletionMean B H q J p
  let f := fun p : Fin B.P ↦ fun D : Y p ↦
    ((canonicalInPart B H J p ∩ D.1).card : ℚ)
  let g := fun p : Fin B.P ↦ fun D : Y p ↦ f p D - mu p
  have hzero : ∀ p, ∑ D : Y p, g p D = 0 := by
    intro p
    have hqp : q p ≤ Fintype.card
        {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
      simpa only [Fintype.card_coe] using hq p
    have hmean := FixedCard.sum_inter_card_eq_mean_mul_card
      (canonicalInPart B H J p) (q p) hqp
    dsimp only [Y, g, f, mu, playerCanonicalDeletionMean]
    rw [Finset.sum_sub_distrib, hmean]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
    ring
  have hvariance : ∀ p,
      (∑ D : Y p, (g p D) ^ 2) ≤ mu p * Fintype.card (Y p) := by
    intro p
    have hqp : q p ≤ Fintype.card
        {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
      simpa only [Fintype.card_coe] using hq p
    exact FixedCard.sum_sq_sub_intersectionMean_le
      (canonicalInPart B H J p) (q p) hqp
  have hproduct := sum_pi_sum_sq_le_of_coordinate_bounds Y g mu hzero hvariance
  simpa only [Y, g, f, mu, canonicalDeletionCharge,
    conditionalCanonicalDeletionMean, playerCanonicalDeletionMean,
    Nat.cast_sum, Finset.sum_sub_distrib] using hproduct

theorem playerCanonicalDeletionMean_le_rate_mul_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t) (p : Fin B.P)
    {delta : ℚ}
    (hrate : (q p : ℚ) ≤ delta * (part B H J p).card) :
    playerCanonicalDeletionMean B H q J p ≤
      delta * (canonicalInPart B H J p).card := by
  let m := Fintype.card
    {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p}
  let a := (canonicalInPart B H J p).card
  have ham : a ≤ m := by
    exact Finset.card_le_univ (canonicalInPart B H J p)
  change (q p : ℚ) * a / m ≤ delta * a
  by_cases hm : m = 0
  · have ha0 : a = 0 := Nat.eq_zero_of_le_zero (hm ▸ ham)
    rw [hm, ha0]
    norm_num
  · have hmpos : (0 : ℚ) < m := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hrate' : (q p : ℚ) ≤ delta * m := by
      simpa only [m, Fintype.card_coe] using hrate
    apply (div_le_iff hmpos).2
    calc
      (q p : ℚ) * a ≤ (delta * m) * a := by
        exact mul_le_mul_of_nonneg_right hrate' (by positivity)
      _ = delta * a * m := by ring

theorem conditionalCanonicalDeletionMean_le_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t) {delta : ℚ}
    (hrate : ∀ p, (q p : ℚ) ≤ delta * (part B H J p).card) :
    conditionalCanonicalDeletionMean B H q J ≤
      delta * (canonicalMatching B H J).card := by
  calc
    conditionalCanonicalDeletionMean B H q J =
        ∑ p : Fin B.P, playerCanonicalDeletionMean B H q J p := rfl
    _ ≤ ∑ p : Fin B.P,
        delta * (canonicalInPart B H J p).card := by
      gcongr with p
      exact playerCanonicalDeletionMean_le_rate_mul_card B H q J p (hrate p)
    _ = delta * ∑ p : Fin B.P,
        ((canonicalInPart B H J p).card : ℚ) := by
      rw [Finset.mul_sum]
    _ = delta * (canonicalMatching B H J).card := by
      congr 1
      have hcards :
          (∑ p : Fin B.P, (canonicalInPart B H J p).card) =
            (canonicalMatching B H J).card := by
        calc
          (∑ p : Fin B.P, (canonicalInPart B H J p).card) =
              ∑ p : Fin B.P,
                (canonicalMatching B H J ∩ part B H J p).card := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact canonicalInPart_card B H J p
          _ = (canonicalMatching B H J).card :=
            sum_canonicalMatching_inter_part_card B H J
      exact_mod_cast hcards

theorem deletionProfile_charge_upper_tail_card_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) {delta a pBad : ℚ}
    (hrate : ∀ p, (q p : ℚ) ≤ delta * (part B H J p).card)
    (ha : 0 < a)
    (hprob :
      (delta * (canonicalMatching B H J).card) / a ^ 2 ≤ pBad) :
    (((Finset.univ.filter fun D : DeletionProfile B H q J ↦
        conditionalCanonicalDeletionMean B H q J + a ≤
          (canonicalDeletionCharge B H q J D : ℚ)).card : ℕ) : ℚ) ≤
      pBad * Fintype.card (DeletionProfile B H q J) := by
  classical
  have hvariance := deletionProfile_sum_sq_charge_sub_mean_le B H q J hq
  have hmeanUpper := conditionalCanonicalDeletionMean_le_rate B H q J hrate
  have hprob' : conditionalCanonicalDeletionMean B H q J / a ^ 2 ≤ pBad :=
    (div_le_div_of_nonneg_right hmeanUpper (sq_nonneg a)).trans hprob
  exact finite_card_upper_tail_le_of_sum_sq_le
    (fun D : DeletionProfile B H q J ↦
      (canonicalDeletionCharge B H q J D : ℚ))
    (conditionalCanonicalDeletionMean B H q J) a
    (conditionalCanonicalDeletionMean B H q J) pBad ha hvariance hprob'

theorem deletionProfile_actual_bad_card_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) {delta a pBad : ℚ}
    (hrate : ∀ p, (q p : ℚ) ≤ delta * (part B H J p).card)
    (ha : 0 < a)
    (hprob :
      (delta * (canonicalMatching B H J).card) / a ^ 2 ≤ pBad)
    {d : ℕ}
    (hthreshold :
      delta * (canonicalMatching B H J).card + a ≤ (d : ℚ)) :
    (((Finset.univ.filter fun D : DeletionProfile B H q J ↦
        d < canonicalDeletionCount (⟨J, D⟩ : Sample B H q)).card : ℕ) : ℚ) ≤
      pBad * Fintype.card (DeletionProfile B H q J) := by
  classical
  let bad := Finset.univ.filter fun D : DeletionProfile B H q J ↦
    d < canonicalDeletionCount (⟨J, D⟩ : Sample B H q)
  let tail := Finset.univ.filter fun D : DeletionProfile B H q J ↦
    conditionalCanonicalDeletionMean B H q J + a ≤
      (canonicalDeletionCharge B H q J D : ℚ)
  have hmeanUpper := conditionalCanonicalDeletionMean_le_rate B H q J hrate
  have hsubset : bad ⊆ tail := by
    intro D hD
    have hbadNat : d < canonicalDeletionCount
        (⟨J, D⟩ : Sample B H q) := (Finset.mem_filter.1 hD).2
    have hbadQ : (d : ℚ) < canonicalDeletionCount
        (⟨J, D⟩ : Sample B H q) := by exact_mod_cast hbadNat
    have hchargeNat := canonicalDeletionCount_le_charge B H q J D
    have hchargeQ :
        (canonicalDeletionCount (⟨J, D⟩ : Sample B H q) : ℚ) ≤
          canonicalDeletionCharge B H q J D := by exact_mod_cast hchargeNat
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ D, ?_⟩
    linarith
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ : (bad.card : ℚ) ≤ (tail.card : ℚ) := by exact_mod_cast hcardNat
  have htail := deletionProfile_charge_upper_tail_card_le
    B H q J hq hrate ha hprob
  change (bad.card : ℚ) ≤ pBad * Fintype.card (DeletionProfile B H q J)
  exact hcardQ.trans htail

theorem canonicalDeletionBadSamples_card_eq_sum_fibers
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (d : ℕ) :
    (canonicalDeletionBadSamples (B := B) (H := H) (q := q) d).card =
      ∑ J : IndexTuple B t,
        (Finset.univ.filter fun D : DeletionProfile B H q J ↦
          d < canonicalDeletionCount (⟨J, D⟩ : Sample B H q)).card := by
  classical
  have hfinset :
      canonicalDeletionBadSamples (B := B) (H := H) (q := q) d =
        (Finset.univ : Finset (IndexTuple B t)).sigma fun J ↦
          Finset.univ.filter fun D : DeletionProfile B H q J ↦
            d < canonicalDeletionCount (⟨J, D⟩ : Sample B H q) := by
    ext s
    simp [canonicalDeletionBadSamples, CanonicalDeletionGood]
  rw [hfinset, Finset.card_sigma]

set_option maxHeartbeats 1000000 in

theorem canonicalDeletionBadBound_of_variance
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card)
    {delta a pBad : ℚ}
    (hrate : ∀ J p, (q p : ℚ) ≤ delta * (part B H J p).card)
    (ha : 0 < a)
    (hprob :
      (delta * (B.edgeCount * r ^ B.P)) / a ^ 2 ≤ pBad)
    {d : ℕ}
    (hthreshold : delta * (B.edgeCount * r ^ B.P) + a ≤ (d : ℚ)) :
    CanonicalDeletionBadBound B H q d pBad := by
  classical
  refine ⟨?_⟩
  rw [canonicalDeletionBadSamples_card_eq_sum_fibers B H q d]
  push_cast
  calc
    (∑ J : IndexTuple B t,
      ((Finset.univ.filter fun D : DeletionProfile B H q J ↦
        d < canonicalDeletionCount (⟨J, D⟩ : Sample B H q)).card : ℚ)) ≤
        ∑ J : IndexTuple B t,
          pBad * Fintype.card (DeletionProfile B H q J) := by
      apply Finset.sum_le_sum
      intro J _hJ
      apply deletionProfile_actual_bad_card_le B H q J (hq J) (hrate J) ha
      · simpa only [canonicalMatching_card B H, Nat.cast_mul, Nat.cast_pow] using hprob
      · simpa only [canonicalMatching_card B H, Nat.cast_mul, Nat.cast_pow] using hthreshold
    _ = pBad * Fintype.card (Sample B H q) := by
      simp_rw [deletionProfile_card B H q, sample_card B H q]
      push_cast
      simp
      ring

theorem div_rate_mul_le_nat_div_add_one
    (numerator denominator N : ℕ) (hdenominator : 0 < denominator) :
    (numerator : ℚ) / denominator * N ≤
      (numerator * N / denominator + 1 : ℕ) := by
  have hdenQ : (0 : ℚ) < denominator := by exact_mod_cast hdenominator
  rw [show (numerator : ℚ) / denominator * N =
    ((numerator * N : ℕ) : ℚ) / denominator by
      push_cast
      ring]
  apply (div_le_iff hdenQ).2
  have hnat := Nat.le_of_lt (Nat.lt_mul_div_succ (numerator * N) hdenominator)
  exact_mod_cast (by simpa only [Nat.mul_comm] using hnat)

theorem canonicalDeletionBadBound_of_variance_div_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card)
    (numerator denominator u : ℕ) (hdenominator : 0 < denominator)
    (hu : 0 < u)
    (hrate : ∀ J p, (q p : ℚ) ≤
      ((numerator : ℚ) / denominator) * (part B H J p).card)
    {pBad : ℚ}
    (hprob :
      ((((numerator : ℚ) / denominator) *
        (B.edgeCount * r ^ B.P)) / (u : ℚ) ^ 2) ≤ pBad) :
    CanonicalDeletionBadBound B H q
      (numerator * (B.edgeCount * r ^ B.P) / denominator + u + 1) pBad := by
  apply canonicalDeletionBadBound_of_variance B H q hq hrate
    (a := (u : ℚ))
  · exact_mod_cast hu
  · exact hprob
  · have hround := div_rate_mul_le_nat_div_add_one
      numerator denominator (B.edgeCount * r ^ B.P) hdenominator
    have hround' :
        (numerator : ℚ) / denominator *
            ((B.edgeCount : ℚ) * (r : ℚ) ^ B.P) ≤
          (numerator * (B.edgeCount * r ^ B.P) / denominator : ℕ) + 1 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hround
    push_cast
    linarith

theorem canonicalDeletionBadBound_of_inverse_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card)
    (denominator u : ℕ) (hdenominator : 0 < denominator) (hu : 0 < u)
    (hrate : ∀ J p, (q p : ℚ) ≤
      ((1 : ℚ) / denominator) * (part B H J p).card)
    (hsquare : 16 * (B.edgeCount * r ^ B.P) ≤ u ^ 2) :
    CanonicalDeletionBadBound B H q
      ((B.edgeCount * r ^ B.P) / denominator + u + 1)
      ((1 : ℚ) / (16 * denominator)) := by
  let N := B.edgeCount * r ^ B.P
  have hdenQ : (0 : ℚ) < denominator := by exact_mod_cast hdenominator
  have huQ : (0 : ℚ) < u := by exact_mod_cast hu
  have hsquareQ : (16 : ℚ) * N ≤ (u : ℚ) ^ 2 := by
    exact_mod_cast hsquare
  have hprob :
      ((((1 : ℚ) / denominator) * N) / (u : ℚ) ^ 2) ≤
        (1 : ℚ) / (16 * denominator) := by
    rw [show ((((1 : ℚ) / denominator) * N) / (u : ℚ) ^ 2) =
        (N : ℚ) / ((denominator : ℚ) * (u : ℚ) ^ 2) by ring]
    apply (div_le_div_iff (mul_pos hdenQ (sq_pos_of_pos huQ))
      (mul_pos (by norm_num : (0 : ℚ) < 16) hdenQ)).2
    have hmul := mul_le_mul_of_nonneg_right hsquareQ hdenQ.le
    calc
      (N : ℚ) * (16 * denominator) = (16 * N) * denominator := by ring
      _ ≤ (u : ℚ) ^ 2 * denominator := hmul
      _ = 1 * (denominator * (u : ℚ) ^ 2) := by ring
  simpa only [one_mul] using
    (canonicalDeletionBadBound_of_variance_div_rate
      B H q hq 1 denominator u hdenominator hu hrate
        (by simpa only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hprob))

theorem floorDeletionCount_badBound_of_inverse_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (denominator u : ℕ) (hdenominator : 0 < denominator) (hu : 0 < u)
    (hsquare : 16 * (B.edgeCount * r ^ B.P) ≤ u ^ 2) :
    CanonicalDeletionBadBound B H
      (floorDeletionCount B r t 1 denominator)
      ((B.edgeCount * r ^ B.P) / denominator + u + 1)
      ((1 : ℚ) / (16 * denominator)) := by
  apply canonicalDeletionBadBound_of_inverse_rate B H
    (floorDeletionCount B r t 1 denominator)
    (floorDeletionCount_admissible B H 1 denominator (by omega))
    denominator u hdenominator hu
  · intro J p
    exact floorDeletionCount_cast_le_rate_mul_part_card
      B H 1 denominator J p hdenominator
  · exact hsquare

end HardDistribution

end Formal.Streaming
