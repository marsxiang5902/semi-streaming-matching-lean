import SemiStreamingMatching.Proofs.Blueprint.Blueprint

open scoped BigOperators

namespace BlueprintUpperBound

abbrev V (B : SimpleProperBlueprint) := Vertex B.P B.C

abbrev Prefix (B : SimpleProperBlueprint) (p : Fin B.P) :=
  (i : Fin B.P) → i < p → Fin B.C

def vertexPrefix (B : SimpleProperBlueprint) (p : Fin B.P) (v : V B) : Prefix B p :=
  fun i _ => v i

def suffixFinset (B : SimpleProperBlueprint) (p : Fin B.P) : Finset (Suffix B.P B.C p) :=
  Finset.univ

def suffixCount (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) : ℕ :=
  ((suffixFinset B p).filter fun s => X (patchVertex p v s)).card

def lowAt (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) : Prop :=
  2 * suffixCount B X p v ≤ (suffixFinset B p).card

def bad (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] (v : V B) : Prop :=
  ∃ p : Fin B.P, lowAt B X p v

def firstLowAt (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) : Prop :=
  lowAt B X p v ∧ ∀ q : Fin B.P, q < p → ¬ lowAt B X q v

lemma patchVertex_eq_of_prefix_eq {B : SimpleProperBlueprint} {p : Fin B.P} {v w : V B}
    (h : vertexPrefix B p v = vertexPrefix B p w) (s : Suffix B.P B.C p) :
    patchVertex p v s = patchVertex p w s := by
  funext i
  by_cases hpi : p ≤ i
  · simp [patchVertex, hpi]
  · have hip : i < p := lt_of_not_ge hpi
    have := congrFun (congrFun h i) hip
    simp only [patchVertex, dif_neg hpi]
    exact this

lemma suffixCount_eq_of_prefix_eq {B : SimpleProperBlueprint} {X : V B → Prop}
    [DecidablePred X] {p : Fin B.P} {v w : V B}
    (h : vertexPrefix B p v = vertexPrefix B p w) :
    suffixCount B X p v = suffixCount B X p w := by
  unfold suffixCount
  apply congrArg Finset.card
  apply Finset.ext
  intro s
  have hs := patchVertex_eq_of_prefix_eq h s
  simp only [Finset.mem_filter]
  rw [hs]

lemma lowAt_iff_of_prefix_eq {B : SimpleProperBlueprint} {X : V B → Prop}
    [DecidablePred X] {p : Fin B.P} {v w : V B}
    (h : vertexPrefix B p v = vertexPrefix B p w) :
    lowAt B X p v ↔ lowAt B X p w := by
  simp only [lowAt, suffixCount_eq_of_prefix_eq h]

lemma vertexPrefix_eq_mono {B : SimpleProperBlueprint} {p q : Fin B.P} {v w : V B}
    (hqp : q ≤ p) (h : vertexPrefix B p v = vertexPrefix B p w) :
    vertexPrefix B q v = vertexPrefix B q w := by
  funext i hi
  have hip : i < p := lt_of_lt_of_le hi hqp
  exact congrFun (congrFun h i) hip

lemma firstLowAt_iff_of_prefix_eq {B : SimpleProperBlueprint} {X : V B → Prop}
    [DecidablePred X] {p : Fin B.P} {v w : V B}
    (h : vertexPrefix B p v = vertexPrefix B p w) :
    firstLowAt B X p v ↔ firstLowAt B X p w := by
  constructor
  · rintro ⟨hp, hbefore⟩
    refine ⟨(lowAt_iff_of_prefix_eq h).mp hp, ?_⟩
    intro q hqp
    have hpref := vertexPrefix_eq_mono (B := B) (v := v) (w := w) (le_of_lt hqp) h
    exact fun hq => hbefore q hqp ((lowAt_iff_of_prefix_eq hpref).mpr hq)
  · rintro ⟨hp, hbefore⟩
    refine ⟨(lowAt_iff_of_prefix_eq h).mpr hp, ?_⟩
    intro q hqp
    have hpref := vertexPrefix_eq_mono (B := B) (v := v) (w := w) (le_of_lt hqp) h
    exact fun hq => hbefore q hqp ((lowAt_iff_of_prefix_eq hpref).mp hq)

noncomputable def lowIndices (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (v : V B) : Finset (Fin B.P) := by
  classical
  exact Finset.univ.filter fun p => lowAt B X p v

lemma lowIndices_nonempty (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) : (lowIndices B X v.1).Nonempty := by
  classical
  rcases v.2 with ⟨p, hp⟩
  exact ⟨p, by simp [lowIndices, hp]⟩

noncomputable def firstIndex (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) : Fin B.P :=
  (lowIndices B X v.1).min' (lowIndices_nonempty B X v)

lemma firstIndex_low (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) :
    lowAt B X (firstIndex B X v) v.1 := by
  classical
  have hmem : firstIndex B X v ∈ lowIndices B X v.1 := by
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

lemma firstIndex_not_low_before (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) (q : Fin B.P)
    (hq : q < firstIndex B X v) : ¬ lowAt B X q v.1 := by
  classical
  intro hlow
  have hmem : q ∈ lowIndices B X v.1 := by simp [lowIndices, hlow]
  have hle : firstIndex B X v ≤ q := by
    unfold firstIndex
    exact (lowIndices B X v.1).min'_le q hmem
  exact (not_le_of_gt hq) hle

lemma firstIndex_firstLowAt (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) :
    firstLowAt B X (firstIndex B X v) v.1 :=
  ⟨firstIndex_low B X v, firstIndex_not_low_before B X v⟩

abbrev FirstKey (B : SimpleProperBlueprint) :=
  Sigma (fun p : Fin B.P => Prefix B p)

noncomputable def firstKey (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] (v : {v : V B // bad B X v}) : FirstKey B :=
  ⟨firstIndex B X v, vertexPrefix B (firstIndex B X v) v.1⟩

def suffixPatchEquiv (B : SimpleProperBlueprint) (p : Fin B.P) (v : V B) :
    Suffix B.P B.C p ≃ {w : V B // vertexPrefix B p w = vertexPrefix B p v} where
  toFun s := ⟨patchVertex p v s, by
    funext i hi
    have hpi : ¬ p ≤ i := not_le_of_gt hi
    simp only [vertexPrefix, patchVertex, dif_neg hpi]⟩
  invFun w := fun i _ => w.1 i
  left_inv s := by
    funext i
    funext hi
    simp [patchVertex, hi]
  right_inv w := by
    apply Subtype.ext
    funext i
    by_cases hpi : p ≤ i
    · simp [patchVertex, hpi]
    · have hip : i < p := lt_of_not_ge hpi
      have hpref := congrFun (congrFun w.2 i) hip
      simpa [vertexPrefix, patchVertex, hpi] using hpref.symm

lemma card_suffix_eq_card_prefixFiber (B : SimpleProperBlueprint) (p : Fin B.P) (v : V B) :
    Fintype.card (Suffix B.P B.C p) =
      Fintype.card {w : V B // vertexPrefix B p w = vertexPrefix B p v} := by
  exact Fintype.card_congr (suffixPatchEquiv B p v)

lemma card_matched_suffix_eq_card_matched_prefixFiber
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) :
    Fintype.card {s : Suffix B.P B.C p // X (patchVertex p v s)} =
      Fintype.card {w : V B //
        vertexPrefix B p w = vertexPrefix B p v ∧ X w} := by
  let e₁ : {s : Suffix B.P B.C p // X (patchVertex p v s)} ≃
      {w : {w : V B // vertexPrefix B p w = vertexPrefix B p v} // X w.1} :=
    (suffixPatchEquiv B p v).subtypeEquiv fun _ => Iff.rfl
  let e₂ : {w : {w : V B // vertexPrefix B p w = vertexPrefix B p v} // X w.1} ≃
      {w : V B // vertexPrefix B p w = vertexPrefix B p v ∧ X w} :=
    { toFun := fun w => ⟨w.1.1, w.1.2, w.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.card_congr (e₁.trans e₂)

lemma suffixCount_eq_card_subtype
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) :
    suffixCount B X p v =
      Fintype.card {s : Suffix B.P B.C p // X (patchVertex p v s)} := by
  classical
  simp [suffixCount, suffixFinset, Fintype.card_subtype]

lemma suffixFinset_card (B : SimpleProperBlueprint) (p : Fin B.P) :
    (suffixFinset B p).card = Fintype.card (Suffix B.P B.C p) := by
  simp [suffixFinset]

noncomputable def prefixFiber (B : SimpleProperBlueprint) (p : Fin B.P) (a : Prefix B p) : Finset (V B) :=
  Finset.univ.filter fun v => vertexPrefix B p v = a

noncomputable def firstMatched (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) : Finset (V B) := by
  classical
  exact Finset.univ.filter fun v => X v ∧ firstLowAt B X p v

noncomputable def firstUnmatched (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) : Finset (V B) := by
  classical
  exact Finset.univ.filter fun v => ¬ X v ∧ firstLowAt B X p v

lemma prefixFiber_card_eq_suffix_card
    (B : SimpleProperBlueprint) (p : Fin B.P) (v : V B) :
    (prefixFiber B p (vertexPrefix B p v)).card = (suffixFinset B p).card := by
  classical
  calc
    (prefixFiber B p (vertexPrefix B p v)).card =
        Fintype.card {w : V B // vertexPrefix B p w = vertexPrefix B p v} := by
      simpa [prefixFiber] using
        (Fintype.card_subtype (fun w : V B => vertexPrefix B p w = vertexPrefix B p v)).symm
    _ = Fintype.card (Suffix B.P B.C p) :=
      (card_suffix_eq_card_prefixFiber B p v).symm
    _ = (suffixFinset B p).card := (suffixFinset_card B p).symm

lemma prefixFiber_filter_card_eq_suffixCount
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X]
    (p : Fin B.P) (v : V B) :
    ((prefixFiber B p (vertexPrefix B p v)).filter X).card = suffixCount B X p v := by
  classical
  calc
    ((prefixFiber B p (vertexPrefix B p v)).filter X).card =
        Fintype.card {w : V B // vertexPrefix B p w = vertexPrefix B p v ∧ X w} := by
      rw [Fintype.card_subtype]
      congr 1
      ext w
      simp [prefixFiber, and_comm]
    _ = Fintype.card {s : Suffix B.P B.C p // X (patchVertex p v s)} :=
      (card_matched_suffix_eq_card_matched_prefixFiber B X p v).symm
    _ = suffixCount B X p v := (suffixCount_eq_card_subtype B X p v).symm

lemma firstMatched_card_le_firstUnmatched_card
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] (p : Fin B.P) :
    (firstMatched B X p).card ≤ (firstUnmatched B X p).card := by
  classical
  let f : V B → Prefix B p := vertexPrefix B p
  have hM : (firstMatched B X p).card =
      ∑ a : Prefix B p,
        ((firstMatched B X p).filter fun v => f v = a).card := by
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
  have hU : (firstUnmatched B X p).card =
      ∑ a : Prefix B p,
        ((firstUnmatched B X p).filter fun v => f v = a).card := by
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
  rw [hM, hU]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hactive : ∃ v : V B, firstLowAt B X p v ∧ f v = a
  · rcases hactive with ⟨v, hvfirst, hvprefix⟩
    subst a
    let F := prefixFiber B p (vertexPrefix B p v)
    have hfirst (w : V B) (hw : vertexPrefix B p w = vertexPrefix B p v) :
        firstLowAt B X p w := by
      exact (firstLowAt_iff_of_prefix_eq hw.symm).mp hvfirst
    have hMf : ((firstMatched B X p).filter fun w => f w = vertexPrefix B p v) =
        F.filter X := by
      ext w
      simp only [Finset.mem_filter, firstMatched, Finset.mem_univ, true_and, F, prefixFiber]
      constructor
      · rintro ⟨⟨hX, _⟩, hpref⟩
        exact ⟨hpref, hX⟩
      · rintro ⟨hpref, hX⟩
        exact ⟨⟨hX, hfirst w hpref⟩, hpref⟩
    have hUf : ((firstUnmatched B X p).filter fun w => f w = vertexPrefix B p v) =
        F.filter fun w => ¬ X w := by
      ext w
      simp only [Finset.mem_filter, firstUnmatched, Finset.mem_univ, true_and, F, prefixFiber]
      constructor
      · rintro ⟨⟨hX, _⟩, hpref⟩
        exact ⟨hpref, hX⟩
      · rintro ⟨hpref, hX⟩
        exact ⟨⟨hX, hfirst w hpref⟩, hpref⟩
    rw [hMf, hUf]
    have hlow := hvfirst.1
    have hhalf : 2 * (F.filter X).card ≤ F.card := by
      change 2 * ((prefixFiber B p (vertexPrefix B p v)).filter X).card ≤
        (prefixFiber B p (vertexPrefix B p v)).card
      rw [prefixFiber_filter_card_eq_suffixCount, prefixFiber_card_eq_suffix_card]
      exact hlow
    have hpartition : F.card = (F.filter X).card + (F.filter fun w => ¬ X w).card := by
      have hu : (F.filter X) ∪ (F.filter fun w => ¬ X w) = F := by
        ext w
        by_cases hw : X w <;> simp [hw]
      have hd : Disjoint (F.filter X) (F.filter fun w => ¬ X w) := by
        apply Finset.disjoint_left.mpr
        intro w hwX hwN
        exact (Finset.mem_filter.mp hwN).2 (Finset.mem_filter.mp hwX).2
      calc
        F.card = ((F.filter X) ∪ (F.filter fun w => ¬ X w)).card := congrArg Finset.card hu.symm
        _ = (F.filter X).card + (F.filter fun w => ¬ X w).card :=
          Finset.card_union_of_disjoint hd
    omega
  · have hMempty : ((firstMatched B X p).filter fun v => f v = a) = ∅ := by
      ext v
      simp only [Finset.mem_filter, firstMatched, Finset.mem_univ, true_and, Finset.not_mem_empty,
        iff_false]
      rintro ⟨⟨_, hfirst⟩, hpref⟩
      exact hactive ⟨v, hfirst, hpref⟩
    have hUempty : ((firstUnmatched B X p).filter fun v => f v = a) = ∅ := by
      ext v
      simp only [Finset.mem_filter, firstUnmatched, Finset.mem_univ, true_and,
        Finset.not_mem_empty, iff_false]
      rintro ⟨⟨_, hfirst⟩, hpref⟩
      exact hactive ⟨v, hfirst, hpref⟩
    simp [hMempty, hUempty]

noncomputable def badMatched (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] : Finset (V B) := by
  classical
  exact Finset.univ.filter fun v => X v ∧ bad B X v

noncomputable def unmatched (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] : Finset (V B) := by
  classical
  exact Finset.univ.filter fun v => ¬ X v

lemma firstLowAt_unique
    {B : SimpleProperBlueprint} {X : V B → Prop} [DecidablePred X]
    {p q : Fin B.P} {v : V B}
    (hp : firstLowAt B X p v) (hq : firstLowAt B X q v) : p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact False.elim (hq.2 p hpq hp.1)
  · exact hpq
  · exact False.elim (hp.2 q hpq hq.1)

lemma firstMatched_pairwise_disjoint
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    ∀ p ∈ (Finset.univ : Finset (Fin B.P)), ∀ q ∈ (Finset.univ : Finset (Fin B.P)),
      p ≠ q → Disjoint (firstMatched B X p) (firstMatched B X q) := by
  classical
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  have hp := (Finset.mem_filter.mp hvp).2.2
  have hq := (Finset.mem_filter.mp hvq).2.2
  exact hpq (firstLowAt_unique hp hq)

lemma firstUnmatched_pairwise_disjoint
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    ∀ p ∈ (Finset.univ : Finset (Fin B.P)), ∀ q ∈ (Finset.univ : Finset (Fin B.P)),
      p ≠ q → Disjoint (firstUnmatched B X p) (firstUnmatched B X q) := by
  classical
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  have hp := (Finset.mem_filter.mp hvp).2.2
  have hq := (Finset.mem_filter.mp hvq).2.2
  exact hpq (firstLowAt_unique hp hq)

lemma biUnion_firstMatched_eq_badMatched
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    (Finset.univ : Finset (Fin B.P)).biUnion (firstMatched B X) = badMatched B X := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨p, _, hvp⟩
    rcases (Finset.mem_filter.mp hvp).2 with ⟨hX, hfirst⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ v, hX, ⟨p, hfirst.1⟩⟩
  · intro hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hX, hbad⟩
    let vb : {w : V B // bad B X w} := ⟨v, hbad⟩
    let p := firstIndex B X vb
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_univ p, ?_⟩
    simp only [firstMatched, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX, firstIndex_firstLowAt B X vb⟩

lemma biUnion_firstUnmatched_subset_unmatched
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    (Finset.univ : Finset (Fin B.P)).biUnion (firstUnmatched B X) ⊆ unmatched B X := by
  classical
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨p, _, hvp⟩
  have hnX := (Finset.mem_filter.mp hvp).2.1
  simp [unmatched, hnX]

lemma badMatched_card_le_unmatched_card
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    (badMatched B X).card ≤ (unmatched B X).card := by
  classical
  calc
    (badMatched B X).card = ∑ p : Fin B.P, (firstMatched B X p).card := by
      rw [← biUnion_firstMatched_eq_badMatched B X]
      exact Finset.card_biUnion (firstMatched_pairwise_disjoint B X)
    _ ≤ ∑ p : Fin B.P, (firstUnmatched B X p).card := by
      exact Finset.sum_le_sum fun p _ => firstMatched_card_le_firstUnmatched_card B X p
    _ = ((Finset.univ : Finset (Fin B.P)).biUnion (firstUnmatched B X)).card := by
      exact (Finset.card_biUnion (firstUnmatched_pairwise_disjoint B X)).symm
    _ ≤ (unmatched B X).card :=
      Finset.card_le_card (biUnion_firstUnmatched_subset_unmatched B X)

abbrev TaggedEdge (B : SimpleProperBlueprint) :=
  {e : B.EdgeOver // e.2 ∈ B.E e.1}

def taggedEdgeLeft (B : SimpleProperBlueprint) (e : TaggedEdge B) : V B := e.1.2.1

def taggedEdgeRight (B : SimpleProperBlueprint) (e : TaggedEdge B) : V B := e.1.2.2

lemma taggedEdgeLeft_injective (B : SimpleProperBlueprint) :
    Function.Injective (taggedEdgeLeft B) := by
  intro e₁ e₂ h
  rcases e₁ with ⟨⟨p₁, l₁, r₁⟩, he₁⟩
  rcases e₂ with ⟨⟨p₂, l₂, r₂⟩, he₂⟩
  simp only [taggedEdgeLeft] at h
  subst l₂
  rcases B.left_matching he₁ he₂ with ⟨hp, hr⟩
  change p₁ = p₂ at hp
  subst p₂
  subst r₂
  rfl

lemma taggedEdgeRight_injective (B : SimpleProperBlueprint) :
    Function.Injective (taggedEdgeRight B) := by
  intro e₁ e₂ h
  rcases e₁ with ⟨⟨p₁, l₁, r₁⟩, he₁⟩
  rcases e₂ with ⟨⟨p₂, l₂, r₂⟩, he₂⟩
  simp only [taggedEdgeRight] at h
  subst r₂
  rcases B.right_matching he₁ he₂ with ⟨hp, hl⟩
  change p₁ = p₂ at hp
  subst p₂
  subst l₂
  rfl

def taggedEdgeToMatchedLeft (B : SimpleProperBlueprint) (e : TaggedEdge B) :
    {v : V B // leftMatched B.E v} :=
  ⟨taggedEdgeLeft B e, ⟨e.1.1, e.1.2.2, e.2⟩⟩

def taggedEdgeToMatchedRight (B : SimpleProperBlueprint) (e : TaggedEdge B) :
    {v : V B // rightMatched B.E v} :=
  ⟨taggedEdgeRight B e, ⟨e.1.1, e.1.2.1, e.2⟩⟩

noncomputable local instance matchedLeftFintype (B : SimpleProperBlueprint) :
    Fintype {v : V B // leftMatched B.E v} := Fintype.ofFinite _

noncomputable local instance matchedRightFintype (B : SimpleProperBlueprint) :
    Fintype {v : V B // rightMatched B.E v} := Fintype.ofFinite _

noncomputable local instance leftMatchedDecidable (B : SimpleProperBlueprint) :
    DecidablePred (leftMatched B.E) := Classical.decPred _

noncomputable local instance rightMatchedDecidable (B : SimpleProperBlueprint) :
    DecidablePred (rightMatched B.E) := Classical.decPred _

lemma taggedEdgeToMatchedLeft_bijective (B : SimpleProperBlueprint) :
    Function.Bijective (taggedEdgeToMatchedLeft B) := by
  constructor
  · intro e₁ e₂ h
    apply taggedEdgeLeft_injective B
    exact congrArg Subtype.val h
  · rintro ⟨l, p, r, he⟩
    exact ⟨⟨⟨p, (l, r)⟩, he⟩, rfl⟩

lemma taggedEdgeToMatchedRight_bijective (B : SimpleProperBlueprint) :
    Function.Bijective (taggedEdgeToMatchedRight B) := by
  constructor
  · intro e₁ e₂ h
    apply taggedEdgeRight_injective B
    exact congrArg Subtype.val h
  · rintro ⟨r, p, l, he⟩
    exact ⟨⟨⟨p, (l, r)⟩, he⟩, rfl⟩

lemma edgeCount_eq_card_matchedLeft (B : SimpleProperBlueprint) :
    B.edgeCount = Fintype.card {v : V B // leftMatched B.E v} := by
  classical
  unfold SimpleProperBlueprint.edgeCount
  exact Fintype.card_congr (Equiv.ofBijective _ (taggedEdgeToMatchedLeft_bijective B))

lemma edgeCount_eq_card_matchedRight (B : SimpleProperBlueprint) :
    B.edgeCount = Fintype.card {v : V B // rightMatched B.E v} := by
  classical
  unfold SimpleProperBlueprint.edgeCount
  exact Fintype.card_congr (Equiv.ofBijective _ (taggedEdgeToMatchedRight_bijective B))

lemma edge_has_bad_endpoint (B : SimpleProperBlueprint) (e : TaggedEdge B) :
    bad B (leftMatched B.E) (taggedEdgeLeft B e) ∨
      bad B (rightMatched B.E) (taggedEdgeRight B e) := by
  classical
  rcases e with ⟨⟨p, l, r⟩, he⟩
  let SL := (suffixFinset B p).filter fun s => leftMatched B.E (patchVertex p l s)
  let SR := (suffixFinset B p).filter fun s => rightMatched B.E (patchVertex p r s)
  have hd : Disjoint SL SR := by
    apply Finset.disjoint_left.mpr
    intro s hsL hsR
    have hL := (Finset.mem_filter.mp hsL).2
    have hR := (Finset.mem_filter.mp hsR).2
    rcases B.bans he s with hnL | hnR
    · exact hnL hL
    · exact hnR hR
  have hsubset : SL ∪ SR ⊆ suffixFinset B p := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (Finset.mem_filter.mp hs).1
    · exact (Finset.mem_filter.mp hs).1
  have hsum : SL.card + SR.card ≤ (suffixFinset B p).card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card hsubset
  have hor : 2 * SL.card ≤ (suffixFinset B p).card ∨
      2 * SR.card ≤ (suffixFinset B p).card := by omega
  rcases hor with hlow | hlow
  · left
    refine ⟨p, ?_⟩
    exact hlow
  · right
    refine ⟨p, ?_⟩
    exact hlow

abbrev BadLeftVertices (B : SimpleProperBlueprint) :=
  ↥(badMatched B (leftMatched B.E))

abbrev BadRightVertices (B : SimpleProperBlueprint) :=
  ↥(badMatched B (rightMatched B.E))

noncomputable def chargeEdge (B : SimpleProperBlueprint) (e : TaggedEdge B) :
    BadLeftVertices B ⊕ BadRightVertices B := by
  classical
  by_cases hL : bad B (leftMatched B.E) (taggedEdgeLeft B e)
  · exact Sum.inl ⟨taggedEdgeLeft B e, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨e.1.1, e.1.2.2, e.2⟩, hL⟩⟩
  · have hR : bad B (rightMatched B.E) (taggedEdgeRight B e) :=
      (edge_has_bad_endpoint B e).resolve_left hL
    exact Sum.inr ⟨taggedEdgeRight B e, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨e.1.1, e.1.2.1, e.2⟩, hR⟩⟩

lemma chargeEdge_injective (B : SimpleProperBlueprint) : Function.Injective (chargeEdge B) := by
  classical
  intro e₁ e₂ h
  unfold chargeEdge at h
  split at h <;> split at h
  · apply taggedEdgeLeft_injective B
    exact congrArg Subtype.val (Sum.inl.inj h)
  · simp at h
  · simp at h
  · apply taggedEdgeRight_injective B
    exact congrArg Subtype.val (Sum.inr.inj h)

lemma edgeCount_le_bad_endpoint_count (B : SimpleProperBlueprint) :
    B.edgeCount ≤
      (badMatched B (leftMatched B.E)).card +
        (badMatched B (rightMatched B.E)).card := by
  classical
  unfold SimpleProperBlueprint.edgeCount
  simpa using Fintype.card_le_of_injective (chargeEdge B) (chargeEdge_injective B)

noncomputable def matched (B : SimpleProperBlueprint) (X : V B → Prop)
    [DecidablePred X] : Finset (V B) :=
  Finset.univ.filter X

lemma matched_card_add_unmatched_card
    (B : SimpleProperBlueprint) (X : V B → Prop) [DecidablePred X] :
    (matched B X).card + (unmatched B X).card = B.vertexCount := by
  classical
  have hu : matched B X ∪ unmatched B X = (Finset.univ : Finset (V B)) := by
    ext v
    by_cases hv : X v <;> simp [matched, unmatched, hv]
  have hd : Disjoint (matched B X) (unmatched B X) := by
    apply Finset.disjoint_left.mpr
    intro v hvM hvU
    exact (Finset.mem_filter.mp hvU).2 (Finset.mem_filter.mp hvM).2
  rw [← Finset.card_union_of_disjoint hd, hu]
  simp [SimpleProperBlueprint.vertexCount]

lemma matchedLeft_card_eq_edgeCount (B : SimpleProperBlueprint) :
    (matched B (leftMatched B.E)).card = B.edgeCount := by
  classical
  rw [edgeCount_eq_card_matchedLeft]
  unfold matched
  exact (Fintype.card_of_subtype
    (Finset.univ.filter (leftMatched B.E)) (by simp)).symm

lemma matchedRight_card_eq_edgeCount (B : SimpleProperBlueprint) :
    (matched B (rightMatched B.E)).card = B.edgeCount := by
  classical
  rw [edgeCount_eq_card_matchedRight]
  unfold matched
  exact (Fintype.card_of_subtype
    (Finset.univ.filter (rightMatched B.E)) (by simp)).symm

lemma three_edgeCount_le_two_vertexCount (B : SimpleProperBlueprint) :
    3 * B.edgeCount ≤ 2 * B.vertexCount := by
  classical
  have hedge := edgeCount_le_bad_endpoint_count B
  have hbadL := badMatched_card_le_unmatched_card B (leftMatched B.E)
  have hbadR := badMatched_card_le_unmatched_card B (rightMatched B.E)
  have hpartL := matched_card_add_unmatched_card B (leftMatched B.E)
  have hpartR := matched_card_add_unmatched_card B (rightMatched B.E)
  rw [matchedLeft_card_eq_edgeCount] at hpartL
  rw [matchedRight_card_eq_edgeCount] at hpartR
  omega

end BlueprintUpperBound

theorem blueprint_value_le_two_thirds_proof (B : SimpleProperBlueprint) :
    B.value ≤ (2 : ℝ) / 3 := by
  have hnat := BlueprintUpperBound.three_edgeCount_le_two_vertexCount B
  have hcount : (3 : ℝ) * (B.edgeCount : ℝ) ≤
      (2 : ℝ) * (B.vertexCount : ℝ) := by
    exact_mod_cast hnat
  have hvertex_nat : 0 < B.vertexCount := by
    unfold SimpleProperBlueprint.vertexCount
    exact Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, B.hC⟩⟩
  have hvertex : (0 : ℝ) < B.vertexCount := by
    exact_mod_cast hvertex_nat
  rw [SimpleProperBlueprint.value]
  apply (div_le_iff hvertex).2
  nlinarith
