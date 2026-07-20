import SemiStreamingMatching.Proofs.Framework.Augmentation
import SemiStreamingMatching.Proofs.Framework.FiniteProbability
import SemiStreamingMatching.Proofs.Framework.StreamingReduction

open scoped BigOperators

namespace Formal.Streaming

namespace HardDistribution

open SimpleExpansion
open AugmentedExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

noncomputable def sigmaDist {A : Type*} [Fintype A]
    {D : A → Type*} [∀ a, Fintype (D a)]
    (P : FiniteDist A) (K : ∀ a, FiniteDist (D a)) :
    FiniteDist (Sigma D) where
  mass x := P.mass x.1 * (K x.1).mass x.2
  mass_nonneg x := mul_nonneg (P.mass_nonneg x.1) ((K x.1).mass_nonneg x.2)
  sum_mass := by
    classical
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    simp_rw [← Finset.mul_sum, (K _).sum_mass, mul_one]
    exact P.sum_mass

@[simp]
theorem sigmaDist_mass {A : Type*} [Fintype A]
    {D : A → Type*} [∀ a, Fintype (D a)]
    (P : FiniteDist A) (K : ∀ a, FiniteDist (D a)) (x : Sigma D) :
    (sigmaDist P K).mass x = P.mass x.1 * (K x.1).mass x.2 :=
  rfl

abbrev BaseEdge (B : SimpleProperBlueprint) :=
  Formal.Streaming.Edge (SimpleExpansion.Left B L) (SimpleExpansion.Right B R)

abbrev PlayerDeletion (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (q : ℕ) :=
  FixedCard {e : BaseEdge (L := L) (R := R) B // e ∈ part B H J p} q

abbrev DeletionProfile (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) (J : IndexTuple B t) :=
  (p : Fin B.P) → PlayerDeletion B H J p (q p)

abbrev Sample (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (q : Fin B.P → ℕ) :=
  Sigma fun J : IndexTuple B t ↦ DeletionProfile B H q J

noncomputable def prefixCompletionEquivSuffix (B : SimpleProperBlueprint)
    (p : Fin B.P) (J : IndexTuple B t) :
    {K // K ∈ prefixCompletions B p J} ≃ SuffixIndexTuple B t p where
  toFun K q := K.1 q.1
  invFun S := ⟨completeWithSuffix p J S, by
    rw [mem_prefixCompletions_iff]
    intro i hi
    simp [completeWithSuffix, not_le_of_gt hi]⟩
  left_inv K := by
    apply Subtype.ext
    funext i
    by_cases hpi : p ≤ i
    · simp [completeWithSuffix, hpi]
    · have hip : i < p := lt_of_not_ge hpi
      have hagree : AgreeBefore p K.1 J :=
        (mem_prefixCompletions_iff B p J K.1).1 K.2
      simp [completeWithSuffix, hpi, (hagree i hip).symm]
  right_inv S := by
    funext q
    simp [completeWithSuffix, q.2]

theorem prefixCompletions_card (B : SimpleProperBlueprint)
    (p : Fin B.P) (J : IndexTuple B t) :
    (prefixCompletions B p J).card =
      Fintype.card (SuffixIndexTuple B t p) := by
  classical
  calc
    (prefixCompletions B p J).card =
        Fintype.card {K // K ∈ prefixCompletions B p J} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (SuffixIndexTuple B t p) :=
      Fintype.card_congr (prefixCompletionEquivSuffix B p J)

theorem edgesAt_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t) :
    (edgesAt B H p K).card = (B.E p).card * r ^ B.P := by
  classical
  rw [edgesAt, Finset.card_biUnion]
  · rw [Finset.sum_const_nat (fun e _he ↦ edgeBox_card B H e K)]
  · intro e he f hf hef
    apply tagged_edgeBoxes_disjoint (B := B) H
      (a := ⟨p, e⟩) (b := ⟨p, f⟩) he hf
    intro hpair
    have hab : (⟨p, e⟩ : B.EdgeOver) = ⟨p, f⟩ := congrArg Prod.fst hpair
    cases hab
    exact hef rfl

theorem part_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P) :
    (part B H J p).card =
      Fintype.card (SuffixIndexTuple B t p) * ((B.E p).card * r ^ B.P) := by
  classical
  rw [part, Finset.card_biUnion]
  · rw [Finset.sum_const_nat (fun K _hK ↦ edgesAt_card B H p K),
      prefixCompletions_card]
  · intro K _hK K' _hK' hne
    exact edgesAt_disjoint (B := B) H (p := p) (p' := p) (K := K) (K' := K')
      (by
        intro hpair
        exact hne (congrArg Prod.snd hpair))

theorem part_card_independent (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (J J' : IndexTuple B t) :
    (part B H J p).card = (part B H J' p).card := by
  rw [part_card, part_card]

def deletionFiberCard (B : SimpleProperBlueprint) (r t : ℕ)
    (q : Fin B.P → ℕ) : ℕ :=
  ∏ p : Fin B.P,
    Nat.choose
      (Fintype.card (SuffixIndexTuple B t p) * ((B.E p).card * r ^ B.P))
      (q p)

theorem playerDeletion_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P) (q : ℕ) :
    Fintype.card (PlayerDeletion B H J p q) =
      Nat.choose
        (Fintype.card (SuffixIndexTuple B t p) * ((B.E p).card * r ^ B.P)) q := by
  rw [FixedCard.card, Fintype.card_coe, part_card]

theorem deletionProfile_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t) :
    Fintype.card (DeletionProfile B H q J) = deletionFiberCard B r t q := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p _hp
  exact playerDeletion_card B H J p (q p)

theorem sample_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) :
    Fintype.card (Sample B H q) =
      Fintype.card (IndexTuple B t) * deletionFiberCard B r t q := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [deletionProfile_card B H q]
  simp

theorem sample_nonempty (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) :
    Nonempty (Sample B H q) := by
  let J : IndexTuple B t := fun _ ↦ ⟨0, H.t_pos⟩
  refine ⟨⟨J, fun p ↦ ?_⟩⟩
  have hp : q p ≤ Fintype.card
      {e : BaseEdge (L := L) (R := R) B // e ∈ part B H J p} := by
    simpa using hq J p
  exact Classical.choice (FixedCard.nonempty (q p) hp)

noncomputable def hiddenIndexDistribution (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) : FiniteDist (IndexTuple B t) := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (IndexTuple B t) := inferInstance
  exact FiniteDist.uniform (IndexTuple B t)

@[simp]
theorem hiddenIndexDistribution_mass (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    (hiddenIndexDistribution B H).mass J =
      1 / Fintype.card (IndexTuple B t) := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (IndexTuple B t) := inferInstance
  simp [hiddenIndexDistribution]

noncomputable def playerDeletionDistribution (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P)
    (q : ℕ) (hq : q ≤ (part B H J p).card) :
    FiniteDist (PlayerDeletion B H J p q) := by
  have hq' : q ≤ Fintype.card
      {e : BaseEdge (L := L) (R := R) B // e ∈ part B H J p} := by
    simpa using hq
  exact FixedCard.uniform q hq'

noncomputable def deletionProfileDistribution (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card) :
    FiniteDist (DeletionProfile B H q J) := by
  letI : Nonempty (DeletionProfile B H q J) := by
    refine ⟨fun p ↦ ?_⟩
    have hp : q p ≤ Fintype.card
        {e : BaseEdge (L := L) (R := R) B // e ∈ part B H J p} := by
      simpa using hq p
    exact Classical.choice (FixedCard.nonempty (q p) hp)
  exact FiniteDist.uniform (DeletionProfile B H q J)

noncomputable def distribution (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) :
    FiniteDist (Sample B H q) :=
  sigmaDist (hiddenIndexDistribution B H)
    (fun J ↦ deletionProfileDistribution B H q J (hq J))

theorem deletionProfileDistribution_mass (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ) (J : IndexTuple B t)
    (hq : ∀ p, q p ≤ (part B H J p).card)
    (D : DeletionProfile B H q J) :
    (deletionProfileDistribution B H q J hq).mass D =
      1 / Fintype.card (DeletionProfile B H q J) :=
  rfl

theorem distribution_mass (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) (s : Sample B H q) :
    (distribution B H q hq).mass s =
      (1 / Fintype.card (IndexTuple B t)) *
        (1 / Fintype.card (DeletionProfile B H q s.1)) := by
  rw [distribution, sigmaDist_mass, hiddenIndexDistribution_mass,
    deletionProfileDistribution_mass]

theorem distribution_mass_eq_uniform (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) (s : Sample B H q) :
    (distribution B H q hq).mass s =
      1 / Fintype.card (Sample B H q) := by
  rw [distribution_mass, deletionProfile_card, sample_card]
  push_cast
  rw [one_div, one_div, one_div, mul_inv_rev]
  ring

theorem finiteDist_ext_mass {Ω : Type*} [Fintype Ω]
    {P Q : FiniteDist Ω} (h : P.mass = Q.mass) : P = Q := by
  cases P
  cases Q
  simp_all

theorem distribution_eq_uniform (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) :
    distribution B H q hq =
      @FiniteDist.uniform (Sample B H q) _ (sample_nonempty B H q hq) := by
  apply finiteDist_ext_mass
  funext s
  exact distribution_mass_eq_uniform B H q hq s

def deletionEdges {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {J : IndexTuple B t} {p : Fin B.P} {q : ℕ}
    (D : PlayerDeletion B H J p q) : Finset (BaseEdge (L := L) (R := R) B) :=
  D.1.image Subtype.val

theorem deletionEdges_subset_part {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {J : IndexTuple B t} {p : Fin B.P} {q : ℕ}
    (D : PlayerDeletion B H J p q) : deletionEdges D ⊆ part B H J p := by
  classical
  intro e he
  rw [deletionEdges, Finset.mem_image] at he
  obtain ⟨z, _hz, rfl⟩ := he
  exact z.2

theorem deletionEdges_card {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {J : IndexTuple B t} {p : Fin B.P} {q : ℕ}
    (D : PlayerDeletion B H J p q) : (deletionEdges D).card = q := by
  classical
  have hcard : (D.1.image Subtype.val).card = D.1.card := by
    rw [Finset.card_image_iff]
    intro a _ b _ hab
    exact Subtype.ext hab
  exact hcard.trans D.2

noncomputable def keptPart {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P → ℕ} (s : Sample B H q) (p : Fin B.P) :
    Finset (BaseEdge (L := L) (R := R) B) :=
  part B H s.1 p \ deletionEdges (s.2 p)

noncomputable def keptEdges {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P → ℕ} (s : Sample B H q) :
    Finset (BaseEdge (L := L) (R := R) B) :=
  Finset.univ.biUnion (keptPart s)

noncomputable def deletedEdges {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    Finset (BaseEdge (L := L) (R := R) B) :=
  Finset.univ.biUnion fun p ↦ deletionEdges (s.2 p)

theorem keptPart_subset_part {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ}
    (s : Sample B H q) (p : Fin B.P) : keptPart s p ⊆ part B H s.1 p :=
  by
    intro e he
    exact (Finset.mem_sdiff.1 he).1

theorem keptEdges_subset_baseGraph {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    keptEdges s ⊆ (SimpleExpansion.graph B H s.1).edges := by
  intro e he
  rw [keptEdges, Finset.mem_biUnion] at he
  obtain ⟨p, _hp, hep⟩ := he
  rw [SimpleExpansion.mem_graph_iff]
  exact ⟨p, keptPart_subset_part s p hep⟩

theorem deletedEdges_card_le_total {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (deletedEdges s).card ≤ ∑ p : Fin B.P, q p := by
  classical
  calc
    (deletedEdges s).card ≤
        ∑ p : Fin B.P, (deletionEdges (s.2 p)).card := by
      exact Finset.card_biUnion_le
    _ = ∑ p : Fin B.P, q p := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact deletionEdges_card (s.2 p)

theorem canonical_sdiff_kept_subset_deletedEdges {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    canonicalMatching B H s.1 \ keptEdges s ⊆ deletedEdges s := by
  intro z hz
  have hzCanonical : z ∈ canonicalMatching B H s.1 := (Finset.mem_sdiff.1 hz).1
  have hzGraph := canonicalMatching_subset_graph B H s.1 hzCanonical
  rw [SimpleExpansion.mem_graph_iff] at hzGraph
  obtain ⟨p, hzPart⟩ := hzGraph
  have hzDeleted : z ∈ deletionEdges (s.2 p) := by
    by_contra hnot
    apply (Finset.mem_sdiff.1 hz).2
    rw [keptEdges, Finset.mem_biUnion]
    exact ⟨p, Finset.mem_univ p,
      Finset.mem_sdiff.2 ⟨hzPart, hnot⟩⟩
  rw [deletedEdges, Finset.mem_biUnion]
  exact ⟨p, Finset.mem_univ p, hzDeleted⟩

theorem canonical_deletion_loss_le {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (canonicalMatching B H s.1 \ keptEdges s).card ≤
      ∑ p : Fin B.P, q p := by
  exact (Finset.card_le_card (canonical_sdiff_kept_subset_deletedEdges s)).trans
    (deletedEdges_card_le_total s)

noncomputable def augmentedGraph {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    BipartiteGraph (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B) :=
  AugmentedExpansion.graph (canonicalMatching B H s.1) (keptEdges s)

noncomputable def externalInput {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :=
  externalMatching (canonicalMatching B H s.1)

theorem liftEdges_disjoint_of_disjoint {B : SimpleProperBlueprint}
    {E F : Finset (BaseEdge (L := L) (R := R) B)} (hEF : Disjoint E F) :
    Disjoint (liftEdges E) (liftEdges F) := by
  classical
  rw [Finset.disjoint_left]
  intro e heE heF
  rw [liftEdges, Finset.mem_image] at heE
  obtain ⟨a, ha, rfl⟩ := heE
  exact Finset.disjoint_left.1 hEF ha (mem_liftEdges_iff.1 heF)

noncomputable def block {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    Fin (B.P + 1) → Finset
      (Formal.Streaming.Edge (AugmentedExpansion.Left (L := L) (R := R) B)
        (AugmentedExpansion.Right (L := L) (R := R) B)) :=
  Fin.lastCases (externalInput s) (fun p ↦ liftEdges (keptPart s p))

@[simp]
theorem block_castSucc {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    (p : Fin B.P) : block s p.castSucc = liftEdges (keptPart s p) := by
  simp [block]

@[simp]
theorem block_last {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    block s (Fin.last B.P) = externalInput s := by
  simp [block]

noncomputable def edgePartition {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    EdgePartition (B.P + 1)
      (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B) where
  block := block s
  disjoint := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨p, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨p', rfl⟩ | rfl
      · have hpp : p ≠ p' := by
          intro h
          exact hij (congrArg Fin.castSucc h)
        simpa only [block_castSucc] using liftEdges_disjoint_of_disjoint (by
          rw [Finset.disjoint_left]
          intro e hep hep'
          exact Finset.disjoint_left.1
            (parts_disjoint (B := B) H s.1 hpp)
            (keptPart_subset_part s p hep)
            (keptPart_subset_part s p' hep'))
      · simpa only [block_castSucc, block_last] using
          liftEdges_disjoint_externalMatching
            (canonicalMatching B H s.1) (keptPart s p)
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨p, rfl⟩ | rfl
      · simpa only [block_castSucc, block_last] using
          (liftEdges_disjoint_externalMatching
            (canonicalMatching B H s.1) (keptPart s p)).symm
      · exact False.elim (hij rfl)

theorem edgePartition_edgeSet {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (edgePartition s).edgeSet =
      liftEdges (keptEdges s) ∪ externalInput s := by
  classical
  ext e
  constructor
  · intro he
    rw [EdgePartition.edgeSet, Finset.mem_biUnion] at he
    obtain ⟨i, _hi, hei⟩ := he
    rcases Fin.eq_castSucc_or_eq_last i with ⟨p, rfl⟩ | rfl
    · apply Finset.mem_union_left
      apply liftEdges_mono (E := keptPart s p)
      · intro z hz
        rw [keptEdges, Finset.mem_biUnion]
        exact ⟨p, Finset.mem_univ p, hz⟩
      · simpa [edgePartition] using hei
    · exact Finset.mem_union_right _ (by simpa [edgePartition] using hei)
  · intro he
    rw [Finset.mem_union] at he
    rw [EdgePartition.edgeSet, Finset.mem_biUnion]
    rcases he with heLift | heExternal
    · rw [liftEdges, Finset.mem_image] at heLift
      obtain ⟨z, hz, rfl⟩ := heLift
      rw [keptEdges, Finset.mem_biUnion] at hz
      obtain ⟨p, _hp, hzp⟩ := hz
      refine ⟨p.castSucc, Finset.mem_univ _, ?_⟩
      simpa [edgePartition] using
        (mem_liftEdges_iff (E := keptPart s p) (e := z)).2 hzp
    · refine ⟨Fin.last B.P, Finset.mem_univ _, ?_⟩
      simpa [edgePartition] using heExternal

theorem edgePartition_graph {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (edgePartition s).graph = augmentedGraph s := by
  apply BipartiteGraph.ext
  change (edgePartition s).edgeSet = (augmentedGraph s).edges
  rw [edgePartition_edgeSet]
  rfl

noncomputable def finitePartitionDistribution
    {L₀ R₀ : Type} [Fintype L₀] [Fintype R₀]
    [DecidableEq L₀] [DecidableEq R₀]
    (B : SimpleProperBlueprint)
    (H : ERSGraph L₀ R₀ B.C r t) (q : Fin B.P → ℕ)
    (hq : ∀ J p, q p ≤ (part B H J p).card) :
    FinitePartitionDistribution (B.P + 1)
      (AugmentedExpansion.Left (L := L₀) (R := R₀) B)
      (AugmentedExpansion.Right (L := L₀) (R := R₀) B) where
  Sample := Sample (L := L₀) (R := R₀) B H q
  sampleFintype := inferInstance
  sampleNonempty := sample_nonempty B H q hq
  input := fun (s : Sample (L := L₀) (R := R₀) B H q) ↦
    edgePartition (B := B) (H := H) (q := q) s

noncomputable def special {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :=
  AugmentedExpansion.specialEdges (canonicalMatching B H s.1) (keptEdges s)

def Present {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    (z : BaseEdge (L := L) (R := R) B) : Prop :=
  z ∈ keptEdges s

noncomputable def potentialSpecialEdges (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :=
  AugmentedExpansion.specialEdges (canonicalMatching B H J)
    (SimpleExpansion.graph B H J).edges

@[simp]
theorem liftEdge_mem_potentialSpecialEdges_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    (z : BaseEdge (L := L) (R := R) B) :
    liftEdge z ∈ potentialSpecialEdges B H J ↔ IsSpecial B H J z := by
  classical
  rw [potentialSpecialEdges, liftEdge_mem_specialEdges_iff]
  rfl

@[simp]
theorem liftEdge_mem_special_iff_present_and_special {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    (z : BaseEdge (L := L) (R := R) B) :
    liftEdge z ∈ special s ↔ Present s z ∧ IsSpecial B H s.1 z := by
  classical
  rw [special, liftEdge_mem_specialEdges_iff]
  constructor
  · rintro ⟨hzKept, hzLeft, hzRight⟩
    exact ⟨hzKept, keptEdges_subset_baseGraph s hzKept, hzLeft, hzRight⟩
  · rintro ⟨hzKept, _hzGraph, hzLeft, hzRight⟩
    exact ⟨hzKept, hzLeft, hzRight⟩

theorem special_subset_potentialSpecialEdges {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    special s ⊆ potentialSpecialEdges B H s.1 := by
  classical
  intro e he
  rw [special, AugmentedExpansion.specialEdges] at he
  rw [potentialSpecialEdges, AugmentedExpansion.specialEdges]
  apply liftEdges_mono (E := keptEdges s |>.filter fun z ↦
    LeftCovered (canonicalMatching B H s.1) z.1 ∧
      RightCovered (canonicalMatching B H s.1) z.2)
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨keptEdges_subset_baseGraph s hz.1, hz.2⟩
  · exact he

theorem inter_special_card_le_inter_potentialSpecialEdges
    {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P → ℕ} (s : Sample B H q)
    (M : Finset (Formal.Streaming.Edge
      (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B))) :
    (M ∩ special s).card ≤
      (M ∩ potentialSpecialEdges B H s.1).card := by
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_inter] at he ⊢
  exact ⟨he.1, special_subset_potentialSpecialEdges s he.2⟩

theorem inter_special_eq_inter_potentialSpecialEdges {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    {M : Finset (Formal.Streaming.Edge
      (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B))}
    (hM : M ⊆ (augmentedGraph s).edges) :
    M ∩ special s = M ∩ potentialSpecialEdges B H s.1 := by
  classical
  ext e
  constructor
  · intro he
    rw [Finset.mem_inter] at he ⊢
    exact ⟨he.1, special_subset_potentialSpecialEdges s he.2⟩
  · intro he
    rw [Finset.mem_inter] at he ⊢
    refine ⟨he.1, ?_⟩
    have heGraph := hM he.1
    rw [potentialSpecialEdges, AugmentedExpansion.specialEdges] at he
    rw [liftEdges, Finset.mem_image] at he
    obtain ⟨z, hzPotential, rfl⟩ := he.2
    change liftEdge z ∈
      (AugmentedExpansion.graph (canonicalMatching B H s.1) (keptEdges s)).edges
      at heGraph
    rw [AugmentedExpansion.graph, Finset.mem_union] at heGraph
    rcases heGraph with heKept | heExternal
    · have hzKept : z ∈ keptEdges s := mem_liftEdges_iff.1 heKept
      rw [special]
      exact liftEdge_mem_specialEdges_iff.2
        ⟨hzKept, (Finset.mem_filter.1 hzPotential).2⟩
    · have hePotentialLift : liftEdge z ∈ liftEdges
          ((SimpleExpansion.graph B H s.1).edges.filter fun w ↦
            LeftCovered (canonicalMatching B H s.1) w.1 ∧
              RightCovered (canonicalMatching B H s.1) w.2) :=
        mem_liftEdges_iff.2 hzPotential
      exact False.elim (Finset.disjoint_left.1
        (liftEdges_disjoint_externalMatching (canonicalMatching B H s.1)
          ((SimpleExpansion.graph B H s.1).edges.filter fun w ↦
            LeftCovered (canonicalMatching B H s.1) w.1 ∧
              RightCovered (canonicalMatching B H s.1) w.2))
        hePotentialLift heExternal)

theorem inter_special_card_eq_inter_potentialSpecialEdges
    {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P → ℕ} (s : Sample B H q)
    {M : Finset (Formal.Streaming.Edge
      (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B))}
    (hM : M ⊆ (augmentedGraph s).edges) :
    (M ∩ special s).card =
      (M ∩ potentialSpecialEdges B H s.1).card := by
  rw [inter_special_eq_inter_potentialSpecialEdges s hM]

theorem inter_special_card_eq_inter_potentialSpecialEdges_of_input
    {B : SimpleProperBlueprint} {H : ERSGraph L R B.C r t}
    {q : Fin B.P → ℕ} (s : Sample B H q)
    {M : Finset (Formal.Streaming.Edge
      (AugmentedExpansion.Left (L := L) (R := R) B)
      (AugmentedExpansion.Right (L := L) (R := R) B))}
    (hM : M ⊆ (edgePartition s).graph.edges) :
    (M ∩ special s).card =
      (M ∩ potentialSpecialEdges B H s.1).card := by
  apply inter_special_card_eq_inter_potentialSpecialEdges s
  rw [← edgePartition_graph]
  exact hM

noncomputable def sampleCertificateWithLoss {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    (d : ℕ)
    (hdeleted : (canonicalMatching B H s.1 \ keptEdges s).card ≤ d) :
    MatchingGapCertificate (edgePartition s).graph where
  special := special s
  optimumLower :=
    2 * Fintype.card (SimpleExpansion.Left B L) -
      (canonicalMatching B H s.1).card - d
  ordinaryUpper :=
    (Fintype.card (SimpleExpansion.Left B L) -
      (canonicalMatching B H s.1).card) +
    (Fintype.card (SimpleExpansion.Right B R) -
      (canonicalMatching B H s.1).card)
  optimumLower_le := by
    rw [edgePartition_graph]
    exact augmented_matchingNumber_lower_bound
      (canonicalMatching_isMatching B H s.1)
      (expansion_side_card_eq B H) hdeleted
  ordinary_part_le := by
    intro M hM
    rw [edgePartition_graph] at hM
    exact matching_erase_special_card_le_of_isMatching
      (canonicalMatching_isMatching B H s.1) hM

@[simp]
theorem sampleCertificateWithLoss_special {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q)
    (d : ℕ)
    (hdeleted : (canonicalMatching B H s.1 \ keptEdges s).card ≤ d) :
    (sampleCertificateWithLoss s d hdeleted).special = special s := by
  rfl

noncomputable def sampleCertificate {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    MatchingGapCertificate (edgePartition s).graph :=
  sampleCertificateWithLoss s (∑ p : Fin B.P, q p)
    (canonical_deletion_loss_le s)

@[simp]
theorem sampleCertificate_special {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (sampleCertificate s).special = special s := by
  rfl

noncomputable def exactSampleCertificate {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    MatchingGapCertificate (edgePartition s).graph :=
  sampleCertificateWithLoss s
    (canonicalMatching B H s.1 \ keptEdges s).card (le_refl _)

@[simp]
theorem exactSampleCertificate_special {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (exactSampleCertificate s).special = special s := by
  rfl

@[simp]
theorem exactSampleCertificate_optimumLower {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (exactSampleCertificate s).optimumLower =
      2 * Fintype.card (SimpleExpansion.Left B L) -
        (canonicalMatching B H s.1).card -
          (canonicalMatching B H s.1 \ keptEdges s).card := by
  rfl

@[simp]
theorem exactSampleCertificate_ordinaryUpper {B : SimpleProperBlueprint}
    {H : ERSGraph L R B.C r t} {q : Fin B.P → ℕ} (s : Sample B H q) :
    (exactSampleCertificate s).ordinaryUpper =
      (Fintype.card (SimpleExpansion.Left B L) -
        (canonicalMatching B H s.1).card) +
      (Fintype.card (SimpleExpansion.Right B R) -
        (canonicalMatching B H s.1).card) := by
  rfl

end HardDistribution

end Formal.Streaming
