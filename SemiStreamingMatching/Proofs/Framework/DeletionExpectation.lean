import SemiStreamingMatching.Proofs.Framework.DeletionConcentration
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Formal.Streaming

theorem sum_pi_apply_eq_card_mul_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, Fintype (X i)]
    (i : ι) (f : X i → ℚ) :
    (∑ x : (∀ j, X j), f (x i)) =
      Fintype.card (∀ j : {j // j ≠ i}, X j) * ∑ a : X i, f a := by
  let e := Equiv.piSplitAt i X
  calc
    (∑ x : (∀ j, X j), f (x i)) =
        ∑ y : X i × (∀ j : {j // j ≠ i}, X j), f y.1 := by
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = Fintype.card (∀ j : {j // j ≠ i}, X j) * ∑ a : X i, f a := by
      simp [Finset.mul_sum]

theorem card_pi_eq_card_mul_card_compl
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (i : ι) :
    Fintype.card (∀ j, X j) =
      Fintype.card (X i) *
        Fintype.card (∀ j : {j // j ≠ i}, X j) := by
  simpa using Fintype.card_congr (Equiv.piSplitAt i X)

namespace FixedCard

variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem card_finsets_containing (e : E) (q : ℕ) (hq0 : 0 < q) :
    ((Finset.univ : Finset (Finset E)).filter
      (fun D ↦ D.card = q ∧ e ∈ D)).card =
      Nat.choose (Fintype.card E - 1) (q - 1) := by
  let source := (Finset.univ.erase e).powersetCard (q - 1)
  have himage : (Finset.univ : Finset (Finset E)).filter
      (fun D ↦ D.card = q ∧ e ∈ D) = source.image (insert e) := by
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
      have heD : e ∉ D := fun he =>
        (Finset.mem_erase.1 (hD.1 he)).1 rfl
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

private def containingEquiv (e : E) (q : ℕ) :
    {D : FixedCard E q // e ∈ D.1} ≃
      {D : Finset E // D.card = q ∧ e ∈ D} where
  toFun D := ⟨D.1.1, D.1.2, D.2⟩
  invFun D := ⟨⟨D.1, D.2.1⟩, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1000000 in
private theorem card_fixedCard_containing (e : E) (q : ℕ) (hq0 : 0 < q) :
    ((Finset.univ : Finset (FixedCard E q)).filter
      (fun D ↦ e ∈ D.1)).card =
      Nat.choose (Fintype.card E - 1) (q - 1) := by
  calc
    ((Finset.univ : Finset (FixedCard E q)).filter
        (fun D ↦ e ∈ D.1)).card =
        Fintype.card {D : FixedCard E q // e ∈ D.1} :=
      by
        simpa using (Fintype.card_coe
          ((Finset.univ : Finset (FixedCard E q)).filter
            (fun D ↦ e ∈ D.1))).symm
    _ = Fintype.card {D : Finset E // D.card = q ∧ e ∈ D} :=
      Fintype.card_congr (containingEquiv e q)
    _ = ((Finset.univ : Finset (Finset E)).filter
        (fun D ↦ D.card = q ∧ e ∈ D)).card := by
      simpa using (Fintype.card_coe
        ((Finset.univ : Finset (Finset E)).filter
          (fun D ↦ D.card = q ∧ e ∈ D)))
    _ = Nat.choose (Fintype.card E - 1) (q - 1) :=
      card_finsets_containing e q hq0

theorem card_mul_sum_inter_card (A : Finset E) (q : ℕ)
    (hq : q ≤ Fintype.card E) :
    Fintype.card E *
        ∑ D : FixedCard E q, (A ∩ D.1).card =
      q * A.card * Fintype.card (FixedCard E q) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.zero_mul, zero_mul, FixedCard.card, Nat.choose_zero_right,
      mul_one]
    have hDempty : ∀ D : FixedCard E 0, D.1 = ∅ := by
      intro D
      exact Finset.card_eq_zero.mp D.2
    simp [hDempty]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hnpos : 0 < Fintype.card E := hqpos.trans_le hq
    have hincidence :
        ∑ D : FixedCard E q, (A ∩ D.1).card =
          A.card * Nat.choose (Fintype.card E - 1) (q - 1) := by
      calc
        ∑ D : FixedCard E q, (A ∩ D.1).card =
            ∑ D : FixedCard E q, ∑ e in A, if e ∈ D.1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro D _hD
          rw [← Finset.filter_mem_eq_inter]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ e in A, ∑ D : FixedCard E q, if e ∈ D.1 then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ _e in A, Nat.choose (Fintype.card E - 1) (q - 1) := by
          apply Finset.sum_congr rfl
          intro e _he
          rw [← card_fixedCard_containing e q hqpos]
          simp
        _ = A.card * Nat.choose (Fintype.card E - 1) (q - 1) := by simp
    rw [hincidence, FixedCard.card]
    have hid := Nat.succ_mul_choose_eq (Fintype.card E - 1) (q - 1)
    have hn : Fintype.card E - 1 + 1 = Fintype.card E :=
      Nat.sub_add_cancel hnpos
    have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
    have hid' : Fintype.card E * Nat.choose (Fintype.card E - 1) (q - 1) =
        Nat.choose (Fintype.card E) q * q := by
      simpa [Nat.succ_eq_add_one, hn, hq'] using hid
    calc
      Fintype.card E *
          (A.card * Nat.choose (Fintype.card E - 1) (q - 1)) =
          A.card * (Fintype.card E *
            Nat.choose (Fintype.card E - 1) (q - 1)) := by ac_rfl
      _ = A.card * (Nat.choose (Fintype.card E) q * q) := by rw [hid']
      _ = q * A.card * Nat.choose (Fintype.card E) q := by ac_rfl

theorem sum_inter_card_le_of_rate (A : Finset E) (q : ℕ)
    (hq : q ≤ Fintype.card E) {δ : ℚ}
    (hrate : (q : ℚ) ≤ δ * Fintype.card E) :
    (∑ D : FixedCard E q, ((A ∩ D.1).card : ℚ)) ≤
      δ * A.card * Fintype.card (FixedCard E q) := by
  by_cases hn : Fintype.card E = 0
  · have hq0 : q = 0 := Nat.eq_zero_of_le_zero (hn ▸ hq)
    subst q
    letI : IsEmpty E := Fintype.card_eq_zero_iff.mp hn
    have hA : A = ∅ := by
      ext e
      exact isEmptyElim e
    subst A
    have hDempty : ∀ D : FixedCard E 0, D.1 = ∅ := by
      intro D
      exact Finset.card_eq_zero.mp D.2
    simp [hDempty]
  · have hnQ : (0 : ℚ) < Fintype.card E := by positivity
    have hexact := card_mul_sum_inter_card A q hq
    have hexactQ :
        (Fintype.card E : ℚ) *
            ∑ D : FixedCard E q, ((A ∩ D.1).card : ℚ) =
          (q : ℚ) * A.card * Fintype.card (FixedCard E q) := by
      exact_mod_cast hexact
    apply (le_of_mul_le_mul_left ?_ hnQ)
    rw [hexactQ]
    calc
      (q : ℚ) * A.card * Fintype.card (FixedCard E q) ≤
          (δ * Fintype.card E) * A.card * Fintype.card (FixedCard E q) := by
        gcongr
      _ = (Fintype.card E : ℚ) *
          (δ * A.card * Fintype.card (FixedCard E q)) := by ring

end FixedCard

namespace HardDistribution

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def canonicalInPart (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P) :
    Finset {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
  classical
  exact (part B H J p).attach.filter fun z ↦
    z.1 ∈ canonicalMatching B H J

set_option maxHeartbeats 1000000 in
theorem image_canonicalInPart (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P) :
    (canonicalInPart B H J p).image Subtype.val =
      canonicalMatching B H J ∩ part B H J p := by
  classical
  ext z
  simp [canonicalInPart, and_comm]

theorem canonicalInPart_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P) :
    (canonicalInPart B H J p).card =
      (canonicalMatching B H J ∩ part B H J p).card := by
  rw [← image_canonicalInPart B H J p]
  exact (Finset.card_image_iff.mpr (by
    intro a _ha b _hb hab
    exact Subtype.ext hab)).symm

set_option maxHeartbeats 1000000 in
theorem image_canonicalInPart_inter_deletion
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (q : ℕ)
    (D : PlayerDeletion B H J p q) :
    ((canonicalInPart B H J p ∩ D.1).image Subtype.val) =
      canonicalMatching B H J ∩ deletionEdges D := by
  classical
  ext z
  constructor
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have haCanonical : a.1 ∈ canonicalMatching B H J ∩ part B H J p := by
      rw [← image_canonicalInPart B H J p, Finset.mem_image]
      exact ⟨a, (Finset.mem_inter.1 ha).1, rfl⟩
    exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 haCanonical).1, by
      rw [deletionEdges, Finset.mem_image]
      exact ⟨a, (Finset.mem_inter.1 ha).2, rfl⟩⟩
  · intro hz
    rcases Finset.mem_inter.1 hz with ⟨hzCanonical, hzDeletion⟩
    rw [deletionEdges, Finset.mem_image] at hzDeletion
    obtain ⟨a, haD, rfl⟩ := hzDeletion
    have haPart : a.1 ∈ part B H J p := a.2
    have haImage : a.1 ∈ (canonicalInPart B H J p).image Subtype.val := by
      rw [image_canonicalInPart B H J p]
      exact Finset.mem_inter.2 ⟨hzCanonical, haPart⟩
    rw [Finset.mem_image] at haImage
    obtain ⟨b, hb, hba⟩ := haImage
    have hsub : b = a := Subtype.ext hba
    subst b
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_inter.2 ⟨hb, haD⟩, rfl⟩

theorem canonicalInPart_inter_deletion_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (q : ℕ)
    (D : PlayerDeletion B H J p q) :
    (canonicalInPart B H J p ∩ D.1).card =
      (canonicalMatching B H J ∩ deletionEdges D).card := by
  rw [← image_canonicalInPart_inter_deletion B H J p q D]
  exact (Finset.card_image_iff.mpr (by
    intro a _ha b _hb hab
    exact Subtype.ext hab)).symm

theorem sum_canonical_inter_playerDeletion_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (q : ℕ)
    (hq : q ≤ (part B H J p).card) {δ : ℚ}
    (hrate : (q : ℚ) ≤ δ * (part B H J p).card) :
    (∑ D : PlayerDeletion B H J p q,
        ((canonicalMatching B H J ∩ deletionEdges D).card : ℚ)) ≤
      δ * (canonicalMatching B H J ∩ part B H J p).card *
        Fintype.card (PlayerDeletion B H J p q) := by
  have hq' : q ≤ Fintype.card
      {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
    simpa using hq
  have hrate' : (q : ℚ) ≤ δ * Fintype.card
      {z : BaseEdge (L := L) (R := R) B // z ∈ part B H J p} := by
    simpa using hrate
  have h := FixedCard.sum_inter_card_le_of_rate
    (canonicalInPart B H J p) q hq' hrate'
  calc
    (∑ D : PlayerDeletion B H J p q,
        ((canonicalMatching B H J ∩ deletionEdges D).card : ℚ)) =
        ∑ D : PlayerDeletion B H J p q,
          ((canonicalInPart B H J p ∩ D.1).card : ℚ) := by
      apply Finset.sum_congr rfl
      intro D _hD
      exact_mod_cast (canonicalInPart_inter_deletion_card B H J p q D).symm
    _ ≤ δ * (canonicalInPart B H J p).card *
        Fintype.card (PlayerDeletion B H J p q) := h
    _ = δ * (canonicalMatching B H J ∩ part B H J p).card *
        Fintype.card (PlayerDeletion B H J p q) := by
      rw [canonicalInPart_card]

theorem canonicalMatching_eq_biUnion_inter_part
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) :
    canonicalMatching B H J =
      Finset.univ.biUnion fun p ↦
        canonicalMatching B H J ∩ part B H J p := by
  classical
  ext z
  constructor
  · intro hz
    have hzGraph := canonicalMatching_subset_graph B H J hz
    rw [mem_graph_iff] at hzGraph
    obtain ⟨p, hzp⟩ := hzGraph
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_univ p, Finset.mem_inter.2 ⟨hz, hzp⟩⟩
  · intro hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨p, _hp, hzp⟩ := hz
    exact (Finset.mem_inter.1 hzp).1

theorem sum_canonicalMatching_inter_part_card
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) :
    (∑ p : Fin B.P,
      (canonicalMatching B H J ∩ part B H J p).card) =
        (canonicalMatching B H J).card := by
  classical
  have hdisj : ∀ p ∈ (Finset.univ : Finset (Fin B.P)),
      ∀ p' ∈ (Finset.univ : Finset (Fin B.P)), p ≠ p' →
        Disjoint (canonicalMatching B H J ∩ part B H J p)
          (canonicalMatching B H J ∩ part B H J p') := by
    intro p _hp p' _hp' hne
    rw [Finset.disjoint_left]
    intro z hzp hzp'
    exact Finset.disjoint_left.1 (parts_disjoint B H J hne)
      (Finset.mem_inter.1 hzp).2 (Finset.mem_inter.1 hzp').2
  calc
    (∑ p : Fin B.P,
      (canonicalMatching B H J ∩ part B H J p).card) =
        (Finset.univ.biUnion fun p ↦
          canonicalMatching B H J ∩ part B H J p).card := by
      symm
      exact Finset.card_biUnion hdisj
    _ = (canonicalMatching B H J).card := by
      rw [← canonicalMatching_eq_biUnion_inter_part B H J]

theorem canonical_sdiff_kept_card_le_sum_inter_deletion
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (s : Sample B H q) :
    (canonicalMatching B H s.1 \ keptEdges s).card ≤
      ∑ p : Fin B.P,
        (canonicalMatching B H s.1 ∩ deletionEdges (s.2 p)).card := by
  classical
  have hsub : canonicalMatching B H s.1 \ keptEdges s ⊆
      Finset.univ.biUnion fun p ↦
        canonicalMatching B H s.1 ∩ deletionEdges (s.2 p) := by
    intro z hz
    have hzdel := canonical_sdiff_kept_subset_deletedEdges s hz
    rw [deletedEdges, Finset.mem_biUnion] at hzdel
    obtain ⟨p, _hp, hzp⟩ := hzdel
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_univ p,
      Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hz).1, hzp⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem deletionProfile_sum_canonical_sdiff_kept_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) {δ : ℚ}
    (hrate : ∀ p, (q p : ℚ) ≤ δ * (part B H J p).card) :
    (∑ D : DeletionProfile B H q J,
        (((canonicalMatching B H J \ keptEdges ⟨J, D⟩).card : ℕ) : ℚ)) ≤
      δ * (canonicalMatching B H J).card *
        Fintype.card (DeletionProfile B H q J) := by
  classical
  calc
    (∑ D : DeletionProfile B H q J,
        (((canonicalMatching B H J \ keptEdges ⟨J, D⟩).card : ℕ) : ℚ)) ≤
        ∑ D : DeletionProfile B H q J,
          ∑ p : Fin B.P,
            ((canonicalMatching B H J ∩ deletionEdges (D p)).card : ℚ) := by
      apply Finset.sum_le_sum
      intro D _hD
      exact_mod_cast canonical_sdiff_kept_card_le_sum_inter_deletion
        B H q (⟨J, D⟩ : Sample B H q)
    _ = ∑ p : Fin B.P,
        ∑ D : DeletionProfile B H q J,
          ((canonicalMatching B H J ∩ deletionEdges (D p)).card : ℚ) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ p : Fin B.P,
        δ * (canonicalMatching B H J ∩ part B H J p).card *
          Fintype.card (DeletionProfile B H q J) := by
      apply Finset.sum_le_sum
      intro p _hp
      let rest := ∀ j : {j : Fin B.P // j ≠ p},
        PlayerDeletion B H J j (q j)
      have hplayer := sum_canonical_inter_playerDeletion_le
        B H J p (q p) (hq p) (hrate p)
      calc
        (∑ D : DeletionProfile B H q J,
          ((canonicalMatching B H J ∩ deletionEdges (D p)).card : ℚ)) =
            Fintype.card rest *
              ∑ D : PlayerDeletion B H J p (q p),
                ((canonicalMatching B H J ∩ deletionEdges D).card : ℚ) := by
          exact sum_pi_apply_eq_card_mul_sum
            (fun j ↦ PlayerDeletion B H J j (q j)) p
              (fun D ↦ ((canonicalMatching B H J ∩ deletionEdges D).card : ℚ))
        _ ≤ Fintype.card rest *
            (δ * (canonicalMatching B H J ∩ part B H J p).card *
              Fintype.card (PlayerDeletion B H J p (q p))) := by
          exact mul_le_mul_of_nonneg_left hplayer (by positivity)
        _ = δ * (canonicalMatching B H J ∩ part B H J p).card *
            Fintype.card (DeletionProfile B H q J) := by
          rw [card_pi_eq_card_mul_card_compl
            (fun j ↦ PlayerDeletion B H J j (q j)) p]
          dsimp only [rest]
          push_cast
          ring
    _ = δ * (canonicalMatching B H J).card *
        Fintype.card (DeletionProfile B H q J) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      have hcards :
          (∑ p : Fin B.P,
            ((canonicalMatching B H J ∩ part B H J p).card : ℚ)) =
              (canonicalMatching B H J).card := by
        exact_mod_cast sum_canonicalMatching_inter_part_card B H J
      rw [hcards]

theorem canonicalDeletionCount_sum_le
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) {δ : ℚ}
    (hrate : ∀ J p, (q p : ℚ) ≤ δ * (part B H J p).card) :
    (∑ s : Sample B H q, (canonicalDeletionCount s : ℚ)) ≤
      δ * (B.edgeCount * r ^ B.P) * Fintype.card (Sample B H q) := by
  classical
  calc
    (∑ s : Sample B H q, (canonicalDeletionCount s : ℚ)) =
        ∑ J : IndexTuple B t, ∑ D : DeletionProfile B H q J,
          (((canonicalMatching B H J \ keptEdges ⟨J, D⟩).card : ℕ) : ℚ) := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      rfl
    _ ≤ ∑ J : IndexTuple B t,
        δ * (canonicalMatching B H J).card *
          Fintype.card (DeletionProfile B H q J) := by
      apply Finset.sum_le_sum
      intro J _hJ
      exact deletionProfile_sum_canonical_sdiff_kept_le
        B H q J (hq J) (hrate J)
    _ = δ * (B.edgeCount * r ^ B.P) * Fintype.card (Sample B H q) := by
      simp_rw [canonicalMatching_card B H,
        deletionProfile_card B H q, sample_card B H q]
      push_cast
      simp
      ring

theorem canonicalDeletionCount_sum_le_of_div_rate
    (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card)
    (hpart : ∀ J p, 0 < (part B H J p).card) {δ : ℚ}
    (hrate : ∀ J p,
      (q p : ℚ) / (part B H J p).card ≤ δ) :
    (∑ s : Sample B H q, (canonicalDeletionCount s : ℚ)) ≤
      δ * (B.edgeCount * r ^ B.P) * Fintype.card (Sample B H q) := by
  apply canonicalDeletionCount_sum_le B H q hq
  intro J p
  have hp : (0 : ℚ) < (part B H J p).card := by
    exact_mod_cast hpart J p
  exact (div_le_iff hp).mp (hrate J p)

set_option maxHeartbeats 1200000 in

structure CanonicalDeletionBadBound (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (d : ℕ)
    (pBad : ℚ) : Prop where
  card_le :
    ((canonicalDeletionBadSamples (B := B) (H := H) (q := q) d).card : ℚ) ≤
      pBad * Fintype.card (Sample B H q)

end HardDistribution

end Formal.Streaming
