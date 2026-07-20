import SemiStreamingMatching.Proofs.Framework.Expansion
import SemiStreamingMatching.Proofs.Framework.HardnessCertificate
import SemiStreamingMatching.Proofs.Framework.VertexCover

namespace Formal.Streaming

namespace AugmentedExpansion

open SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

abbrev BaseLeft (B : SimpleProperBlueprint) := SimpleExpansion.Left B L
abbrev BaseRight (B : SimpleProperBlueprint) := SimpleExpansion.Right B R

abbrev Left (B : SimpleProperBlueprint) := Sum (BaseLeft (L := L) B) (BaseRight (R := R) B)

abbrev Right (B : SimpleProperBlueprint) := Sum (BaseRight (R := R) B) (BaseLeft (L := L) B)

def uncoveredLeft {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (BaseLeft (L := L) B) :=
  Finset.univ \ M.image Prod.fst

def uncoveredRight {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (BaseRight (R := R) B) :=
  Finset.univ \ M.image Prod.snd

@[simp]
theorem mem_uncoveredLeft_iff {B : SimpleProperBlueprint}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {l : BaseLeft (L := L) B} :
    l ∈ uncoveredLeft M ↔ ¬ LeftCovered M l := by
  simp [uncoveredLeft, LeftCovered]

@[simp]
theorem mem_uncoveredRight_iff {B : SimpleProperBlueprint}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {v : BaseRight (R := R) B} :
    v ∈ uncoveredRight M ↔ ¬ RightCovered M v := by
  simp [uncoveredRight, RightCovered]

def liftEdge {B : SimpleProperBlueprint}
    (e : Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B)) :
    Formal.Streaming.Edge (Left (L := L) (R := R) B) (Right (L := L) (R := R) B) :=
  (Sum.inl e.1, Sum.inl e.2)

def liftEdges {B : SimpleProperBlueprint}
    (E : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)) :=
  E.image liftEdge

@[simp]
theorem mem_liftEdges_iff {B : SimpleProperBlueprint}
    {E : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {e : Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B)} :
    liftEdge e ∈ liftEdges E ↔ e ∈ E := by
  classical
  constructor
  · rw [liftEdges, Finset.mem_image]
    rintro ⟨f, hf, hfe⟩
    have : f = e := by
      apply Prod.ext
      · exact Sum.inl_injective (congrArg Prod.fst hfe)
      · exact Sum.inl_injective (congrArg Prod.snd hfe)
    simpa [this] using hf
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem liftEdges_card {B : SimpleProperBlueprint}
    (E : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (liftEdges E).card = E.card := by
  classical
  rw [liftEdges, Finset.card_image_iff]
  intro e _ f _ hef
  apply Prod.ext
  · exact Sum.inl_injective (congrArg Prod.fst hef)
  · exact Sum.inl_injective (congrArg Prod.snd hef)

noncomputable def leftExternal {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
    (Right (L := L) (R := R) B)) := by
  classical
  exact (uncoveredLeft M).image fun l ↦
    (Sum.inl l, Sum.inr l)

noncomputable def rightExternal {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
    (Right (L := L) (R := R) B)) := by
  classical
  exact (uncoveredRight M).image fun v ↦
    (Sum.inr v, Sum.inl v)

noncomputable def externalMatching {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)) :=
  leftExternal M ∪ rightExternal M

theorem leftExternal_card {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (leftExternal M).card = (uncoveredLeft M).card := by
  classical
  rw [leftExternal, Finset.card_image_iff]
  intro a _ b _ hab
  exact Sum.inl_injective (congrArg Prod.fst hab)

theorem rightExternal_card {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (rightExternal M).card = (uncoveredRight M).card := by
  classical
  rw [rightExternal, Finset.card_image_iff]
  intro a _ b _ hab
  exact Sum.inr_injective (congrArg Prod.fst hab)

theorem leftExternal_disjoint_rightExternal {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Disjoint (leftExternal M) (rightExternal M) := by
  classical
  rw [Finset.disjoint_left]
  intro e heL heR
  rw [leftExternal, Finset.mem_image] at heL
  rw [rightExternal, Finset.mem_image] at heR
  obtain ⟨l, _, rfl⟩ := heL
  obtain ⟨v, _, h⟩ := heR
  exact Sum.noConfusion (congrArg Prod.fst h)

theorem externalMatching_card {B : SimpleProperBlueprint}
    (M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (externalMatching M).card =
      (uncoveredLeft M).card + (uncoveredRight M).card := by
  rw [externalMatching, Finset.card_union_of_disjoint
    (leftExternal_disjoint_rightExternal M), leftExternal_card, rightExternal_card]

theorem uncoveredLeft_card_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hM : G₀.IsMatching M) :
    (uncoveredLeft M).card = Fintype.card (BaseLeft (L := L) B) - M.card := by
  classical
  rw [uncoveredLeft, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  rw [show (M.image Prod.fst).card = M.card by
    simpa [BipartiteGraph.leftEndpoints] using
      BipartiteGraph.leftEndpoints_card_of_isMatching hM]

theorem uncoveredRight_card_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hM : G₀.IsMatching M) :
    (uncoveredRight M).card = Fintype.card (BaseRight (R := R) B) - M.card := by
  classical
  rw [uncoveredRight, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  rw [show (M.image Prod.snd).card = M.card by
    simpa [BipartiteGraph.rightEndpoints] using
      BipartiteGraph.rightEndpoints_card_of_isMatching hM]

theorem externalMatching_card_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hM : G₀.IsMatching M) :
    (externalMatching M).card =
      (Fintype.card (BaseLeft (L := L) B) - M.card) +
        (Fintype.card (BaseRight (R := R) B) - M.card) := by
  rw [externalMatching_card, uncoveredLeft_card_of_isMatching hM,
    uncoveredRight_card_of_isMatching hM]

theorem externalMatching_left_unique {B : SimpleProperBlueprint}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ externalMatching M) (hf : f ∈ externalMatching M)
    (hleft : e.1 = f.1) : e = f := by
  classical
  rw [externalMatching, Finset.mem_union] at he hf
  rcases he with heL | heR <;> rcases hf with hfL | hfR
  · rw [leftExternal, Finset.mem_image] at heL hfL
    obtain ⟨l, _hl, rfl⟩ := heL
    obtain ⟨l', _hl', rfl⟩ := hfL
    have hll : l = l' := Sum.inl_injective hleft
    subst l'
    rfl
  · rw [leftExternal, Finset.mem_image] at heL
    rw [rightExternal, Finset.mem_image] at hfR
    obtain ⟨l, _hl, rfl⟩ := heL
    obtain ⟨v, _hv, rfl⟩ := hfR
    exact False.elim (Sum.noConfusion hleft)
  · rw [rightExternal, Finset.mem_image] at heR
    rw [leftExternal, Finset.mem_image] at hfL
    obtain ⟨v, _hv, rfl⟩ := heR
    obtain ⟨l, _hl, rfl⟩ := hfL
    exact False.elim (Sum.noConfusion hleft)
  · rw [rightExternal, Finset.mem_image] at heR hfR
    obtain ⟨v, _hv, rfl⟩ := heR
    obtain ⟨v', _hv', rfl⟩ := hfR
    have hvv : v = v' := Sum.inr_injective hleft
    subst v'
    rfl

theorem externalMatching_right_unique {B : SimpleProperBlueprint}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ externalMatching M) (hf : f ∈ externalMatching M)
    (hright : e.2 = f.2) : e = f := by
  classical
  rw [externalMatching, Finset.mem_union] at he hf
  rcases he with heL | heR <;> rcases hf with hfL | hfR
  · rw [leftExternal, Finset.mem_image] at heL hfL
    obtain ⟨l, _hl, rfl⟩ := heL
    obtain ⟨l', _hl', rfl⟩ := hfL
    have hll : l = l' := Sum.inr_injective hright
    subst l'
    rfl
  · rw [leftExternal, Finset.mem_image] at heL
    rw [rightExternal, Finset.mem_image] at hfR
    obtain ⟨l, _hl, rfl⟩ := heL
    obtain ⟨v, _hv, rfl⟩ := hfR
    exact False.elim (Sum.noConfusion hright)
  · rw [rightExternal, Finset.mem_image] at heR
    rw [leftExternal, Finset.mem_image] at hfL
    obtain ⟨v, _hv, rfl⟩ := heR
    obtain ⟨l, _hl, rfl⟩ := hfL
    exact False.elim (Sum.noConfusion hright)
  · rw [rightExternal, Finset.mem_image] at heR hfR
    obtain ⟨v, _hv, rfl⟩ := heR
    obtain ⟨v', _hv', rfl⟩ := hfR
    have hvv : v = v' := Sum.inl_injective hright
    subst v'
    rfl

noncomputable def graph {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B)))
    (kept : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    BipartiteGraph (Left (L := L) (R := R) B) (Right (L := L) (R := R) B) where
  edges := liftEdges kept ∪ externalMatching canonical

theorem externalMatching_isMatching {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (graph canonical kept).IsMatching (externalMatching canonical) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact Finset.mem_union_right _ he
  · intro e f he hf hleft
    exact externalMatching_left_unique he hf hleft
  · intro e f he hf hright
    exact externalMatching_right_unique he hf hright

noncomputable def survivingMatching {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)) :=
  liftEdges (canonical ∩ kept) ∪ externalMatching canonical

theorem liftEdges_disjoint_externalMatching {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Disjoint (liftEdges kept) (externalMatching canonical) := by
  classical
  rw [Finset.disjoint_left]
  intro e heLift heExt
  rw [liftEdges, Finset.mem_image] at heLift
  obtain ⟨z, _hz, rfl⟩ := heLift
  rw [externalMatching, Finset.mem_union] at heExt
  rcases heExt with heL | heR
  · rw [leftExternal, Finset.mem_image] at heL
    obtain ⟨l, _hl, h⟩ := heL
    exact Sum.noConfusion (congrArg Prod.snd h)
  · rw [rightExternal, Finset.mem_image] at heR
    obtain ⟨v, _hv, h⟩ := heR
    exact Sum.noConfusion (congrArg Prod.fst h)

theorem survivingMatching_card {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (survivingMatching canonical kept).card =
      (canonical ∩ kept).card + (externalMatching canonical).card := by
  rw [survivingMatching, Finset.card_union_of_disjoint, liftEdges_card]
  exact liftEdges_disjoint_externalMatching canonical (canonical ∩ kept)

theorem liftEdges_mono {B : SimpleProperBlueprint}
    {E F : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hEF : E ⊆ F) : liftEdges E ⊆ liftEdges F := by
  classical
  intro e he
  rw [liftEdges, Finset.mem_image] at he ⊢
  obtain ⟨z, hz, rfl⟩ := he
  exact ⟨z, hEF hz, rfl⟩

theorem liftEdges_left_unique_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hM : G₀.IsMatching M)
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ liftEdges M) (hf : f ∈ liftEdges M) (hleft : e.1 = f.1) :
    e = f := by
  classical
  rw [liftEdges, Finset.mem_image] at he hf
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, rfl⟩ := hf
  have habLeft : a.1 = b.1 := Sum.inl_injective hleft
  rw [hM.2.1 ha hb habLeft]

theorem liftEdges_right_unique_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {M : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hM : G₀.IsMatching M)
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ liftEdges M) (hf : f ∈ liftEdges M) (hright : e.2 = f.2) :
    e = f := by
  classical
  rw [liftEdges, Finset.mem_image] at he hf
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, rfl⟩ := hf
  have habRight : a.2 = b.2 := Sum.inl_injective hright
  rw [hM.2.2 ha hb habRight]

theorem surviving_lift_external_left_ne {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (_hcanonical : G₀.IsMatching canonical)
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ liftEdges (canonical ∩ kept))
    (hf : f ∈ externalMatching canonical) : e.1 ≠ f.1 := by
  classical
  intro hleft
  rw [liftEdges, Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  have haCanonical : a ∈ canonical := (Finset.mem_inter.1 ha).1
  rw [externalMatching, Finset.mem_union] at hf
  rcases hf with hfL | hfR
  · rw [leftExternal, Finset.mem_image] at hfL
    obtain ⟨l, hl, rfl⟩ := hfL
    have hal : a.1 = l := Sum.inl_injective hleft
    have hlNot : ¬ LeftCovered canonical l := mem_uncoveredLeft_iff.1 hl
    apply hlNot
    rw [← hal]
    exact ⟨a.2, haCanonical⟩
  · rw [rightExternal, Finset.mem_image] at hfR
    obtain ⟨v, _hv, rfl⟩ := hfR
    exact Sum.noConfusion hleft

theorem surviving_lift_external_right_ne {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (_hcanonical : G₀.IsMatching canonical)
    {e f : Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)}
    (he : e ∈ liftEdges (canonical ∩ kept))
    (hf : f ∈ externalMatching canonical) : e.2 ≠ f.2 := by
  classical
  intro hright
  rw [liftEdges, Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  have haCanonical : a ∈ canonical := (Finset.mem_inter.1 ha).1
  rw [externalMatching, Finset.mem_union] at hf
  rcases hf with hfL | hfR
  · rw [leftExternal, Finset.mem_image] at hfL
    obtain ⟨l, _hl, rfl⟩ := hfL
    exact Sum.noConfusion hright
  · rw [rightExternal, Finset.mem_image] at hfR
    obtain ⟨v, hv, rfl⟩ := hfR
    have hav : a.2 = v := Sum.inl_injective hright
    have hvNot : ¬ RightCovered canonical v := mem_uncoveredRight_iff.1 hv
    apply hvNot
    rw [← hav]
    exact ⟨a.1, haCanonical⟩

theorem survivingMatching_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical) :
    (graph canonical kept).IsMatching (survivingMatching canonical kept) := by
  have hsurvivingBase : G₀.IsMatching (canonical ∩ kept) :=
    hcanonical.subset (by
      intro e he
      exact (Finset.mem_inter.1 he).1)
  refine ⟨?_, ?_, ?_⟩
  · rw [survivingMatching]
    change liftEdges (canonical ∩ kept) ∪ externalMatching canonical ⊆
      liftEdges kept ∪ externalMatching canonical
    intro e he
    rcases Finset.mem_union.1 he with heLift | heExt
    · apply Finset.mem_union_left
      exact liftEdges_mono (by
        intro z hz
        exact (Finset.mem_inter.1 hz).2) heLift
    · exact Finset.mem_union_right _ heExt
  · intro e f he hf hleft
    rw [survivingMatching, Finset.mem_union] at he hf
    rcases he with heLift | heExt <;> rcases hf with hfLift | hfExt
    · exact liftEdges_left_unique_of_isMatching hsurvivingBase heLift hfLift hleft
    · exact False.elim (surviving_lift_external_left_ne hcanonical heLift hfExt hleft)
    · exact False.elim (surviving_lift_external_left_ne hcanonical hfLift heExt hleft.symm)
    · exact externalMatching_left_unique heExt hfExt hleft
  · intro e f he hf hright
    rw [survivingMatching, Finset.mem_union] at he hf
    rcases he with heLift | heExt <;> rcases hf with hfLift | hfExt
    · exact liftEdges_right_unique_of_isMatching hsurvivingBase heLift hfLift hright
    · exact False.elim (surviving_lift_external_right_ne hcanonical heLift hfExt hright)
    · exact False.elim (surviving_lift_external_right_ne hcanonical hfLift heExt hright.symm)
    · exact externalMatching_right_unique heExt hfExt hright

theorem survivingMatching_card_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical) :
    (survivingMatching canonical kept).card =
      (canonical ∩ kept).card +
        ((Fintype.card (BaseLeft (L := L) B) - canonical.card) +
          (Fintype.card (BaseRight (R := R) B) - canonical.card)) := by
  rw [survivingMatching_card, externalMatching_card_of_isMatching hcanonical]

theorem survivingMatching_card_of_isMatching_side_eq {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical)
    (hside : Fintype.card (BaseLeft (L := L) B) =
      Fintype.card (BaseRight (R := R) B)) :
    (survivingMatching canonical kept).card =
      (canonical ∩ kept).card +
        2 * (Fintype.card (BaseLeft (L := L) B) - canonical.card) := by
  rw [survivingMatching_card_of_isMatching hcanonical, ← hside]
  omega

theorem survivingMatching_card_lower_bound {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical)
    (hside : Fintype.card (BaseLeft (L := L) B) =
      Fintype.card (BaseRight (R := R) B))
    {d : ℕ} (hdeleted : (canonical \ kept).card ≤ d) :
    2 * Fintype.card (BaseLeft (L := L) B) - canonical.card - d ≤
      (survivingMatching canonical kept).card := by
  have hleftCard : canonical.card ≤ Fintype.card (BaseLeft (L := L) B) := by
    have hle := Finset.card_le_card
      (Finset.subset_univ (BipartiteGraph.leftEndpoints canonical))
    rw [BipartiteGraph.leftEndpoints_card_of_isMatching hcanonical] at hle
    exact hle
  have hsplit : (canonical \ kept).card + (canonical ∩ kept).card = canonical.card := by
    exact Finset.card_sdiff_add_card_inter canonical kept
  have hcard := survivingMatching_card_of_isMatching_side_eq
    (kept := kept) hcanonical hside
  omega

theorem augmented_matchingNumber_lower_bound {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical)
    (hside : Fintype.card (BaseLeft (L := L) B) =
      Fintype.card (BaseRight (R := R) B))
    {d : ℕ} (hdeleted : (canonical \ kept).card ≤ d) :
    2 * Fintype.card (BaseLeft (L := L) B) - canonical.card - d ≤
      (graph canonical kept).matchingNumber := by
  exact (survivingMatching_card_lower_bound hcanonical hside hdeleted).trans
    ((graph canonical kept).matching_card_le
      (survivingMatching_isMatching hcanonical))

noncomputable def specialEdges {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B)))
    (kept : Finset (Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B)) := by
  classical
  exact liftEdges (kept.filter fun e ↦
    LeftCovered canonical e.1 ∧ RightCovered canonical e.2)

@[simp]
theorem liftEdge_mem_specialEdges_iff {B : SimpleProperBlueprint}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {e : Formal.Streaming.Edge (BaseLeft (L := L) B) (BaseRight (R := R) B)} :
    liftEdge e ∈ specialEdges canonical kept ↔
      e ∈ kept ∧ LeftCovered canonical e.1 ∧ RightCovered canonical e.2 := by
  classical
  rw [specialEdges, mem_liftEdges_iff]
  simp only [Finset.mem_filter]

theorem specialEdges_subset_graph {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    specialEdges canonical kept ⊆ (graph canonical kept).edges := by
  classical
  intro e he
  rw [specialEdges] at he
  apply Finset.mem_union_left
  exact liftEdges_mono (by
    intro z hz
    exact (Finset.mem_filter.1 hz).1) he

def nonspecialLeftCover {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Left (L := L) (R := R) B) :=
  (uncoveredLeft canonical).image fun l ↦ Sum.inl l

def nonspecialRightCover {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    Finset (Right (L := L) (R := R) B) :=
  (uncoveredRight canonical).image fun v ↦ Sum.inl v

theorem nonspecialLeftCover_card {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (nonspecialLeftCover canonical).card = (uncoveredLeft canonical).card := by
  classical
  rw [nonspecialLeftCover, Finset.card_image_iff]
  intro l _ l' _ h
  exact Sum.inl_injective h

theorem nonspecialRightCover_card {B : SimpleProperBlueprint}
    (canonical : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (nonspecialRightCover canonical).card = (uncoveredRight canonical).card := by
  classical
  rw [nonspecialRightCover, Finset.card_image_iff]
  intro v _ v' _ h
  exact Sum.inl_injective h

noncomputable def nonspecialGraph {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    BipartiteGraph (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B) where
  edges := (graph canonical kept).edges \ specialEdges canonical kept

theorem nonspecialVertexCover {B : SimpleProperBlueprint}
    (canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))) :
    (nonspecialGraph canonical kept).IsVertexCover
      (nonspecialLeftCover canonical) (nonspecialRightCover canonical) := by
  classical
  intro e he
  have heGraph : e ∈ (graph canonical kept).edges := (Finset.mem_sdiff.1 he).1
  have heNotSpecial : e ∉ specialEdges canonical kept := (Finset.mem_sdiff.1 he).2
  rw [graph, Finset.mem_union] at heGraph
  rcases heGraph with heLift | heExternal
  · rw [liftEdges, Finset.mem_image] at heLift
    obtain ⟨z, hzKept, rfl⟩ := heLift
    by_cases hleft : LeftCovered canonical z.1
    · right
      rw [nonspecialRightCover, Finset.mem_image]
      refine ⟨z.2, ?_, rfl⟩
      rw [mem_uncoveredRight_iff]
      intro hright
      exact heNotSpecial (liftEdge_mem_specialEdges_iff.2
        ⟨hzKept, hleft, hright⟩)
    · left
      rw [nonspecialLeftCover, Finset.mem_image]
      exact ⟨z.1, mem_uncoveredLeft_iff.2 hleft, rfl⟩
  · rw [externalMatching, Finset.mem_union] at heExternal
    rcases heExternal with heLeft | heRight
    · rw [leftExternal, Finset.mem_image] at heLeft
      obtain ⟨l, hl, rfl⟩ := heLeft
      left
      rw [nonspecialLeftCover, Finset.mem_image]
      exact ⟨l, hl, rfl⟩
    · rw [rightExternal, Finset.mem_image] at heRight
      obtain ⟨v, hv, rfl⟩ := heRight
      right
      rw [nonspecialRightCover, Finset.mem_image]
      exact ⟨v, hv, rfl⟩

theorem eraseSpecial_isMatching {B : SimpleProperBlueprint}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {M : Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B))}
    (hM : (graph canonical kept).IsMatching M) :
    (nonspecialGraph canonical kept).IsMatching
      (M \ specialEdges canonical kept) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [nonspecialGraph, Finset.mem_sdiff]
    exact ⟨hM.1 (Finset.mem_sdiff.1 he).1, (Finset.mem_sdiff.1 he).2⟩
  · intro e f he hf hleft
    exact hM.2.1 (Finset.mem_sdiff.1 he).1 (Finset.mem_sdiff.1 hf).1 hleft
  · intro e f he hf hright
    exact hM.2.2 (Finset.mem_sdiff.1 he).1 (Finset.mem_sdiff.1 hf).1 hright

theorem matching_erase_special_card_le {B : SimpleProperBlueprint}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {M : Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B))}
    (hM : (graph canonical kept).IsMatching M) :
    (M \ specialEdges canonical kept).card ≤
      (uncoveredLeft canonical).card + (uncoveredRight canonical).card := by
  have hbound := BipartiteGraph.matching_card_le_vertexCover
    (eraseSpecial_isMatching hM) (nonspecialVertexCover canonical kept)
  simpa [nonspecialLeftCover_card, nonspecialRightCover_card] using hbound

theorem nonspecial_matching_card_le {B : SimpleProperBlueprint}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    {M : Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B))}
    (hM : (graph canonical kept).IsMatching M)
    (hdisjoint : Disjoint M (specialEdges canonical kept)) :
    M.card ≤ (uncoveredLeft canonical).card + (uncoveredRight canonical).card := by
  have hdiff : M \ specialEdges canonical kept = M := by
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · exact fun h ↦ h.1
    · intro he
      exact ⟨he, fun hes ↦ Finset.disjoint_left.1 hdisjoint he hes⟩
  simpa [hdiff] using matching_erase_special_card_le hM

theorem matching_erase_special_card_le_of_isMatching {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical)
    {M : Finset (Formal.Streaming.Edge (Left (L := L) (R := R) B)
      (Right (L := L) (R := R) B))}
    (hM : (graph canonical kept).IsMatching M) :
    (M \ specialEdges canonical kept).card ≤
      (Fintype.card (BaseLeft (L := L) B) - canonical.card) +
        (Fintype.card (BaseRight (R := R) B) - canonical.card) := by
  simpa [uncoveredLeft_card_of_isMatching hcanonical,
    uncoveredRight_card_of_isMatching hcanonical] using
      matching_erase_special_card_le hM

noncomputable def matchingGapCertificate {B : SimpleProperBlueprint}
    {G₀ : BipartiteGraph (BaseLeft (L := L) B) (BaseRight (R := R) B)}
    {canonical kept : Finset (Formal.Streaming.Edge
      (BaseLeft (L := L) B) (BaseRight (R := R) B))}
    (hcanonical : G₀.IsMatching canonical)
    (hside : Fintype.card (BaseLeft (L := L) B) =
      Fintype.card (BaseRight (R := R) B))
    (d : ℕ) (hdeleted : (canonical \ kept).card ≤ d) :
    MatchingGapCertificate (graph canonical kept) where
  special := specialEdges canonical kept
  optimumLower :=
    2 * Fintype.card (BaseLeft (L := L) B) - canonical.card - d
  ordinaryUpper :=
    (Fintype.card (BaseLeft (L := L) B) - canonical.card) +
      (Fintype.card (BaseRight (R := R) B) - canonical.card)
  optimumLower_le := augmented_matchingNumber_lower_bound hcanonical hside hdeleted
  ordinary_part_le := by
    intro M hM
    exact matching_erase_special_card_le_of_isMatching hcanonical hM

end AugmentedExpansion

end Formal.Streaming
