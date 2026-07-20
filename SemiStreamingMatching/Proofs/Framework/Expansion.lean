import SemiStreamingMatching.Proofs.Blueprint.Blueprint
import SemiStreamingMatching.Proofs.Framework.ERS
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Formal.Streaming

namespace SimpleExpansion

variable {L R : Type*} {r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

abbrev Left (B : SimpleProperBlueprint) (L : Type*) := Fin B.P → L

abbrev Right (B : SimpleProperBlueprint) (R : Type*) := Fin B.P → R

abbrev IndexTuple (B : SimpleProperBlueprint) (t : ℕ) := Fin B.P → Fin t

def blueprintEdges (B : SimpleProperBlueprint) : Finset B.EdgeOver :=
  Finset.univ.filter fun e ↦ e.2 ∈ B.E e.1

@[simp]
theorem mem_blueprintEdges_iff (B : SimpleProperBlueprint) (e : B.EdgeOver) :
    e ∈ blueprintEdges B ↔ e.2 ∈ B.E e.1 := by
  simp [blueprintEdges]

theorem blueprintEdges_card (B : SimpleProperBlueprint) :
    (blueprintEdges B).card = B.edgeCount := by
  classical
  rw [SimpleProperBlueprint.edgeCount]
  symm
  apply Fintype.card_ofFinset (blueprintEdges B)

def edgeBox (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (e : _root_.Edge B.P B.C) (K : IndexTuple B t) :
    Finset (Formal.Streaming.Edge (Left B L) (Right B R)) :=
  Finset.univ.filter fun z ↦
    ∀ q, (z.1 q, z.2 q) ∈ H.matching (K q) (e.1 q) (e.2 q)

@[simp]
theorem mem_edgeBox_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (e : _root_.Edge B.P B.C)
    (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    z ∈ edgeBox B H e K ↔
      ∀ q, (z.1 q, z.2 q) ∈ H.matching (K q) (e.1 q) (e.2 q) := by
  simp [edgeBox]

abbrev BoxChoice (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (e : _root_.Edge B.P B.C) (K : IndexTuple B t) :=
  (q : Fin B.P) →
    { a : Formal.Streaming.Edge L R //
      a ∈ H.matching (K q) (e.1 q) (e.2 q) }

def edgeBoxEquiv (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (e : _root_.Edge B.P B.C) (K : IndexTuple B t) :
    { z // z ∈ edgeBox B H e K } ≃ BoxChoice B H e K where
  toFun z q := ⟨(z.1.1 q, z.1.2 q), (mem_edgeBox_iff B H e K z.1).1 z.2 q⟩
  invFun a := ⟨(fun q ↦ (a q).1.1, fun q ↦ (a q).1.2), by
    rw [mem_edgeBox_iff]
    exact fun q ↦ (a q).2⟩
  left_inv z := by
    apply Subtype.ext
    ext q <;> rfl
  right_inv a := by
    funext q
    apply Subtype.ext
    rfl

theorem edgeBox_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (e : _root_.Edge B.P B.C)
    (K : IndexTuple B t) :
    (edgeBox B H e K).card = r ^ B.P := by
  classical
  calc
    (edgeBox B H e K).card = Fintype.card { z // z ∈ edgeBox B H e K } :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (BoxChoice B H e K) :=
      Fintype.card_congr (edgeBoxEquiv B H e K)
    _ = Finset.univ.prod (fun q : Fin B.P ↦
        Fintype.card { a : Formal.Streaming.Edge L R //
          a ∈ H.matching (K q) (e.1 q) (e.2 q) }) := Fintype.card_pi
    _ = Finset.univ.prod (fun _q : Fin B.P ↦ r) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [Fintype.card_coe, H.matching_card]
    _ = r ^ B.P := by simp

theorem edgeBox_left_unique (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) {e : _root_.Edge B.P B.C}
    {K : IndexTuple B t}
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ edgeBox B H e K) (hw : w ∈ edgeBox B H e K)
    (hleft : z.1 = w.1) : z = w := by
  have hcoord : ∀ q, (z.1 q, z.2 q) = (w.1 q, w.2 q) := by
    intro q
    exact (H.matching_isMatching (K q) (e.1 q) (e.2 q)).2.1
      ((mem_edgeBox_iff B H e K z).1 hz q)
      ((mem_edgeBox_iff B H e K w).1 hw q)
      (congrFun hleft q)
  apply Prod.ext hleft
  funext q
  exact congrArg Prod.snd (hcoord q)

theorem edgeBox_right_unique (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) {e : _root_.Edge B.P B.C}
    {K : IndexTuple B t}
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ edgeBox B H e K) (hw : w ∈ edgeBox B H e K)
    (hright : z.2 = w.2) : z = w := by
  have hcoord : ∀ q, (z.1 q, z.2 q) = (w.1 q, w.2 q) := by
    intro q
    exact (H.matching_isMatching (K q) (e.1 q) (e.2 q)).2.2
      ((mem_edgeBox_iff B H e K z).1 hz q)
      ((mem_edgeBox_iff B H e K w).1 hw q)
      (congrFun hright q)
  apply Prod.ext
  · funext q
    exact congrArg Prod.fst (hcoord q)
  · exact hright

def edgesAt (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (p : Fin B.P) (K : IndexTuple B t) :
    Finset (Formal.Streaming.Edge (Left B L) (Right B R)) :=
  (B.E p).biUnion fun e ↦ edgeBox B H e K

@[simp]
theorem mem_edgesAt_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    z ∈ edgesAt B H p K ↔ ∃ e ∈ B.E p, z ∈ edgeBox B H e K := by
  simp [edgesAt]

def AgreeBefore (p : Fin B.P) (K J : IndexTuple B t) : Prop :=
  ∀ q, q < p → K q = J q

noncomputable def prefixCompletions (B : SimpleProperBlueprint) (p : Fin B.P)
    (J : IndexTuple B t) : Finset (IndexTuple B t) := by
  classical
  exact Finset.univ.filter fun K ↦ AgreeBefore p K J

@[simp]
theorem mem_prefixCompletions_iff (B : SimpleProperBlueprint)
    (p : Fin B.P) (J K : IndexTuple B t) :
    K ∈ prefixCompletions B p J ↔ AgreeBefore p K J := by
  simp [prefixCompletions]

noncomputable def part (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) :
    Finset (Formal.Streaming.Edge (Left B L) (Right B R)) :=
  (prefixCompletions B p J).biUnion fun K ↦ edgesAt B H p K

@[simp]
theorem mem_part_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) (p : Fin B.P)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    z ∈ part B H J p ↔
      ∃ K, AgreeBefore p K J ∧ z ∈ edgesAt B H p K := by
  simp [part]

noncomputable def graph (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t) : BipartiteGraph (Left B L) (Right B R) where
  edges := Finset.univ.biUnion fun p ↦ part B H J p

@[simp]
theorem mem_graph_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    z ∈ (graph B H J).edges ↔ ∃ p, z ∈ part B H J p := by
  simp [graph]

def canonicalMatching (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    Finset (Formal.Streaming.Edge (Left B L) (Right B R)) :=
  (blueprintEdges B).biUnion fun e ↦ edgeBox B H e.2 J

@[simp]
theorem mem_canonicalMatching_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    z ∈ canonicalMatching B H J ↔
      ∃ e : B.EdgeOver, e.2 ∈ B.E e.1 ∧ z ∈ edgeBox B H e.2 J := by
  simp [canonicalMatching]

def LeftCovered (M : Finset (Formal.Streaming.Edge (Left B L) (Right B R)))
    (l : Left B L) : Prop := ∃ v, (l, v) ∈ M

def RightCovered (M : Finset (Formal.Streaming.Edge (Left B L) (Right B R)))
    (v : Right B R) : Prop := ∃ l, (l, v) ∈ M

def IsSpecial (B : SimpleProperBlueprint) (H : ERSGraph L R B.C r t)
    (J : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) : Prop :=
  z ∈ (graph B H J).edges ∧
    LeftCovered (canonicalMatching B H J) z.1 ∧
    RightCovered (canonicalMatching B H J) z.2

theorem indexTuple_eq_of_mem_boxes (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {e f : _root_.Edge B.P B.C} {K K' : IndexTuple B t}
    {z : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ edgeBox B H e K) (hz' : z ∈ edgeBox B H f K') :
    K = K' := by
  funext q
  by_contra hq
  have heq : (z.1 q, z.2 q) ∈ H.matchingGroup (K q) := by
    rw [H.mem_matchingGroup_iff]
    exact ⟨e.1 q, e.2 q, (mem_edgeBox_iff B H e K z).1 hz q⟩
  have hef : (z.1 q, z.2 q) ∈ H.matchingGroup (K' q) := by
    rw [H.mem_matchingGroup_iff]
    exact ⟨f.1 q, f.2 q, (mem_edgeBox_iff B H f K' z).1 hz' q⟩
  exact H.not_mem_matchingGroup_of_mem_of_ne hq heq hef

theorem blueprint_left_eq_of_box_left_eq (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {e f : _root_.Edge B.P B.C} {K : IndexTuple B t}
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ edgeBox B H e K) (hw : w ∈ edgeBox B H f K)
    (hleft : z.1 = w.1) : e.1 = f.1 := by
  funext q
  exact H.left_label_eq_of_endpoint_eq
    ((mem_edgeBox_iff B H e K z).1 hz q)
    ((mem_edgeBox_iff B H f K w).1 hw q)
    (congrFun hleft q)

theorem blueprint_right_eq_of_box_right_eq (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {e f : _root_.Edge B.P B.C} {K : IndexTuple B t}
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ edgeBox B H e K) (hw : w ∈ edgeBox B H f K)
    (hright : z.2 = w.2) : e.2 = f.2 := by
  funext q
  exact H.right_label_eq_of_endpoint_eq
    ((mem_edgeBox_iff B H e K z).1 hz q)
    ((mem_edgeBox_iff B H f K w).1 hw q)
    (congrFun hright q)

theorem box_data_unique (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {a b : B.EdgeOver} (ha : a.2 ∈ B.E a.1) (hb : b.2 ∈ B.E b.1)
    {K K' : IndexTuple B t}
    {z : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hza : z ∈ edgeBox B H a.2 K) (hzb : z ∈ edgeBox B H b.2 K') :
    a = b ∧ K = K' := by
  have hK : K = K' := indexTuple_eq_of_mem_boxes B H hza hzb
  subst K'
  rcases a with ⟨p, ⟨al, ar⟩⟩
  rcases b with ⟨p', ⟨bl, br⟩⟩
  dsimp at ha hb hza hzb ⊢
  have hleft : al = bl :=
    blueprint_left_eq_of_box_left_eq B H hza hzb rfl
  subst bl
  obtain ⟨hp, hright⟩ := B.left_matching ha hb
  subst p'
  subst br
  exact ⟨rfl, rfl⟩

theorem tagged_edgeBoxes_disjoint (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {a b : B.EdgeOver} (ha : a.2 ∈ B.E a.1) (hb : b.2 ∈ B.E b.1)
    {K K' : IndexTuple B t} (hne : (a, K) ≠ (b, K')) :
    Disjoint (edgeBox B H a.2 K) (edgeBox B H b.2 K') := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  exact hne (by
    obtain ⟨hab, hKK⟩ := box_data_unique B H ha hb hza hzb
    exact Prod.ext hab hKK)

theorem edgesAt_disjoint (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t)
    {p p' : Fin B.P} {K K' : IndexTuple B t}
    (hne : (p, K) ≠ (p', K')) :
    Disjoint (edgesAt B H p K) (edgesAt B H p' K') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_edgesAt_iff] at hz hz'
  obtain ⟨e, he, hze⟩ := hz
  obtain ⟨f, hf, hzf⟩ := hz'
  let a : B.EdgeOver := ⟨p, e⟩
  let b : B.EdgeOver := ⟨p', f⟩
  have ha : a.2 ∈ B.E a.1 := by simpa [a] using he
  have hb : b.2 ∈ B.E b.1 := by simpa [b] using hf
  have hdata := box_data_unique B H ha hb hze hzf
  exact hne (Prod.ext (congrArg Sigma.fst hdata.1) hdata.2)

theorem parts_disjoint (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    {p p' : Fin B.P} (hne : p ≠ p') :
    Disjoint (part B H J p) (part B H J p') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_part_iff] at hz hz'
  obtain ⟨K, _hK, hzK⟩ := hz
  obtain ⟨K', _hK', hzK'⟩ := hz'
  exact Finset.disjoint_left.mp
    (edgesAt_disjoint (B := B) H (K := K) (K' := K') (by
      intro hpair
      exact hne (congrArg Prod.fst hpair))) hzK hzK'

theorem graph_edge_partition (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    (graph B H J).edges = Finset.univ.biUnion (part B H J) ∧
      ∀ {p p' : Fin B.P}, p ≠ p' →
        Disjoint (part B H J p) (part B H J p') := by
  exact ⟨rfl, fun hne ↦ parts_disjoint B H J hne⟩

theorem canonicalMatching_eq_union_edgesAt (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    canonicalMatching B H J = Finset.univ.biUnion fun p ↦ edgesAt B H p J := by
  ext z
  simp [canonicalMatching, edgesAt, blueprintEdges]

theorem canonicalMatching_subset_graph (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    canonicalMatching B H J ⊆ (graph B H J).edges := by
  intro z hz
  rw [mem_canonicalMatching_iff] at hz
  obtain ⟨e, he, hze⟩ := hz
  rw [mem_graph_iff]
  refine ⟨e.1, ?_⟩
  rw [mem_part_iff]
  refine ⟨J, fun _ _ ↦ rfl, ?_⟩
  rw [mem_edgesAt_iff]
  exact ⟨e.2, he, hze⟩

theorem canonicalMatching_left_unique (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ canonicalMatching B H J)
    (hw : w ∈ canonicalMatching B H J) (hleft : z.1 = w.1) : z = w := by
  rw [mem_canonicalMatching_iff] at hz hw
  obtain ⟨a, ha, hza⟩ := hz
  obtain ⟨b, hb, hwb⟩ := hw
  rcases a with ⟨p, ⟨al, ar⟩⟩
  rcases b with ⟨p', ⟨bl, br⟩⟩
  dsimp at ha hb hza hwb ⊢
  have hlabels : al = bl :=
    blueprint_left_eq_of_box_left_eq B H hza hwb hleft
  subst bl
  obtain ⟨hp, hright⟩ := B.left_matching ha hb
  subst p'
  subst br
  exact edgeBox_left_unique B H hza hwb hleft

theorem canonicalMatching_right_unique (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    {z w : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hz : z ∈ canonicalMatching B H J)
    (hw : w ∈ canonicalMatching B H J) (hright : z.2 = w.2) : z = w := by
  rw [mem_canonicalMatching_iff] at hz hw
  obtain ⟨a, ha, hza⟩ := hz
  obtain ⟨b, hb, hwb⟩ := hw
  rcases a with ⟨p, ⟨al, ar⟩⟩
  rcases b with ⟨p', ⟨bl, br⟩⟩
  dsimp at ha hb hza hwb ⊢
  have hlabels : ar = br :=
    blueprint_right_eq_of_box_right_eq B H hza hwb hright
  subst br
  obtain ⟨hp, hleft⟩ := B.right_matching ha hb
  subst p'
  subst bl
  exact edgeBox_right_unique B H hza hwb hright

theorem canonicalMatching_isMatching (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    (graph B H J).IsMatching (canonicalMatching B H J) := by
  refine ⟨canonicalMatching_subset_graph B H J, ?_, ?_⟩
  · intro z w hz hw hleft
    exact canonicalMatching_left_unique B H J hz hw hleft
  · intro z w hz hw hright
    exact canonicalMatching_right_unique B H J hz hw hright

theorem canonicalMatching_card (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t) :
    (canonicalMatching B H J).card = B.edgeCount * r ^ B.P := by
  classical
  rw [canonicalMatching]
  rw [Finset.card_biUnion]
  · rw [Finset.sum_const_nat (fun e _he ↦ edgeBox_card B H e.2 J)]
    rw [blueprintEdges_card]
  · intro a ha b hb hab
    exact tagged_edgeBoxes_disjoint B H
      ((mem_blueprintEdges_iff B a).1 ha)
      ((mem_blueprintEdges_iff B b).1 hb)
      (by intro hpair; exact hab (congrArg Prod.fst hpair))

theorem expansion_left_card (B : SimpleProperBlueprint) :
    Fintype.card (Left B L) = (Fintype.card L) ^ B.P := by
  classical
  simp [Left, Fintype.card_pi]

theorem expansion_right_card (B : SimpleProperBlueprint) :
    Fintype.card (Right B R) = (Fintype.card R) ^ B.P := by
  classical
  simp [Right, Fintype.card_pi]

theorem expansion_side_card_eq (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) :
    Fintype.card (Left B L) = Fintype.card (Right B R) := by
  rw [expansion_left_card, expansion_right_card, H.side_card_eq]

theorem special_edge_index_witness (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    {p : Fin B.P} {K : IndexTuple B t}
    {z : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hprefix : AgreeBefore p K J) (hz : z ∈ edgesAt B H p K)
    (hspecial : IsSpecial B H J z) :
    ∃ q, p ≤ q ∧ K q = J q := by
  rw [mem_edgesAt_iff] at hz
  obtain ⟨e, he, hze⟩ := hz
  rcases hspecial with ⟨_hgraph, ⟨fv, hf⟩, ⟨gl, hg⟩⟩
  rw [mem_canonicalMatching_iff] at hf hg
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  by_contra hnowitness
  have hne : ∀ q, p ≤ q → K q ≠ J q := by
    intro q hpq hq
    exact hnowitness ⟨q, hpq, hq⟩
  have hleftBefore : ∀ q, q < p → e.1 q = a.2.1 q := by
    intro q hqp
    have hzq := (mem_edgeBox_iff B H e K z).1 hze q
    have hfq := (mem_edgeBox_iff B H a.2 J (z.1, fv)).1 hfa q
    rw [hprefix q hqp] at hzq
    exact H.left_label_eq_of_endpoint_eq hzq hfq rfl
  have hrightBefore : ∀ q, q < p → e.2 q = b.2.2 q := by
    intro q hqp
    have hzq := (mem_edgeBox_iff B H e K z).1 hze q
    have hgq := (mem_edgeBox_iff B H b.2 J (gl, z.2)).1 hgb q
    rw [hprefix q hqp] at hzq
    exact H.right_label_eq_of_endpoint_eq hzq hgq rfl
  have hsuffixLabels : ∀ q, p ≤ q → a.2.1 q = b.2.2 q := by
    intro q hpq
    have hzq := (mem_edgeBox_iff B H e K z).1 hze q
    have hfq := (mem_edgeBox_iff B H a.2 J (z.1, fv)).1 hfa q
    have hgq := (mem_edgeBox_iff B H b.2 J (gl, z.2)).1 hgb q
    have hzGroup : (z.1 q, z.2 q) ∈ H.matchingGroup (K q) := by
      rw [H.mem_matchingGroup_iff]
      exact ⟨e.1 q, e.2 q, hzq⟩
    exact H.induced_same_label (hne q hpq) hzGroup
      (H.edge_mem_groups hfq).1 (H.edge_mem_groups hgq).2
  let x : Suffix B.P B.C p := fun q _ ↦ a.2.1 q
  have hpatchLeft : patchVertex p e.1 x = a.2.1 := by
    funext q
    by_cases hpq : p ≤ q
    · simp [patchVertex, hpq, x]
    · have hqp : q < p := lt_of_not_ge hpq
      simp [patchVertex, hpq, hleftBefore q hqp]
  have hpatchRight : patchVertex p e.2 x = b.2.2 := by
    funext q
    by_cases hpq : p ≤ q
    · simp [patchVertex, hpq, x, hsuffixLabels q hpq]
    · have hqp : q < p := lt_of_not_ge hpq
      simp [patchVertex, hpq, hrightBefore q hqp]
  have hleftMatched : leftMatched B.E (patchVertex p e.1 x) := by
    rw [hpatchLeft]
    exact ⟨a.1, a.2.2, ha⟩
  have hrightMatched : rightMatched B.E (patchVertex p e.2 x) := by
    rw [hpatchRight]
    exact ⟨b.1, b.2.1, hb⟩
  rcases B.bans he x with hban | hban
  · exact hban hleftMatched
  · exact hban hrightMatched

theorem weak_inducedness (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (J : IndexTuple B t)
    {p : Fin B.P} {K : IndexTuple B t}
    {z : Formal.Streaming.Edge (Left B L) (Right B R)}
    (hprefix : AgreeBefore p K J) (hz : z ∈ edgesAt B H p K)
    (hdifferent : ∀ q, p ≤ q → K q ≠ J q) :
    ¬ IsSpecial B H J z := by
  intro hspecial
  obtain ⟨q, hpq, hq⟩ :=
    special_edge_index_witness B H J hprefix hz hspecial
  exact hdifferent q hpq hq

section FiniteUnionBound

variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateFiber (target : I → Fin t) (i : I) : Finset (I → Fin t) :=
  Finset.univ.filter fun J ↦ J i = target i

noncomputable def coordinateHits (target : I → Fin t) : Finset (I → Fin t) := by
  classical
  exact Finset.univ.biUnion (coordinateFiber target)

@[simp]
theorem mem_coordinateFiber_iff (target : I → Fin t) (i : I) (J : I → Fin t) :
    J ∈ coordinateFiber target i ↔ J i = target i := by
  simp [coordinateFiber]

@[simp]
theorem mem_coordinateHits_iff (target : I → Fin t) (J : I → Fin t) :
    J ∈ coordinateHits target ↔ ∃ i, J i = target i := by
  classical
  simp [coordinateHits]

def coordinateFiberTimesValueEquiv (target : I → Fin t) (i : I) :
    ({J // J ∈ coordinateFiber target i} × Fin t) ≃ (I → Fin t) where
  toFun x := Function.update x.1.1 i x.2
  invFun J := (⟨Function.update J i (target i), by
    simp [coordinateFiber]⟩, J i)
  left_inv x := by
    rcases x with ⟨⟨J, hJ⟩, a⟩
    have hJi : J i = target i := by
      simpa [coordinateFiber] using hJ
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [hJi]
      · simp [Function.update_noteq, hji]
    · simp
  right_inv J := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_noteq, hji]

theorem coordinateFiber_card_mul (target : I → Fin t) (i : I) :
    (coordinateFiber target i).card * t = Fintype.card (I → Fin t) := by
  classical
  calc
    (coordinateFiber target i).card * t =
        Fintype.card ({J // J ∈ coordinateFiber target i} × Fin t) := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    _ = Fintype.card (I → Fin t) :=
      Fintype.card_congr (coordinateFiberTimesValueEquiv target i)

theorem coordinateHits_card_mul_le (target : I → Fin t) :
    (coordinateHits target).card * t ≤
      Fintype.card I * Fintype.card (I → Fin t) := by
  classical
  have hunion :
      (coordinateHits target).card ≤
        Finset.univ.sum (fun i : I ↦ (coordinateFiber target i).card) := by
    exact Finset.card_biUnion_le
  calc
    (coordinateHits target).card * t ≤
        Finset.univ.sum (fun i : I ↦ (coordinateFiber target i).card) * t :=
      Nat.mul_le_mul_right t hunion
    _ = Finset.univ.sum (fun i : I ↦ (coordinateFiber target i).card * t) :=
      Finset.sum_mul _ _ _
    _ = Finset.univ.sum (fun _i : I ↦ Fintype.card (I → Fin t)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coordinateFiber_card_mul target i
    _ = Fintype.card I * Fintype.card (I → Fin t) := by simp

end FiniteUnionBound

abbrev SuffixCoordinates (B : SimpleProperBlueprint) (p : Fin B.P) :=
  {q : Fin B.P // p ≤ q}

abbrev SuffixIndexTuple (B : SimpleProperBlueprint) (t : ℕ) (p : Fin B.P) :=
  SuffixCoordinates B p → Fin t

def completeWithSuffix (p : Fin B.P) (K : IndexTuple B t)
    (S : SuffixIndexTuple B t p) : IndexTuple B t :=
  fun q ↦ if h : p ≤ q then S ⟨q, h⟩ else K q

theorem agreeBefore_completeWithSuffix (p : Fin B.P) (K : IndexTuple B t)
    (S : SuffixIndexTuple B t p) :
    AgreeBefore p K (completeWithSuffix p K S) := by
  intro q hqp
  simp [completeWithSuffix, not_le_of_gt hqp]

@[simp]
theorem completeWithSuffix_at (p : Fin B.P) (K : IndexTuple B t)
    (S : SuffixIndexTuple B t p) (q : SuffixCoordinates B p) :
    completeWithSuffix p K S q.1 = S q := by
  simp [completeWithSuffix, q.2]

noncomputable def survivingSuffixes (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R)) :
    Finset (SuffixIndexTuple B t p) := by
  classical
  exact Finset.univ.filter fun S ↦
    IsSpecial B H (completeWithSuffix p K S) z

@[simp]
theorem mem_survivingSuffixes_iff (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R))
    (S : SuffixIndexTuple B t p) :
    S ∈ survivingSuffixes B H p K z ↔
      IsSpecial B H (completeWithSuffix p K S) z := by
  classical
  simp [survivingSuffixes]

theorem survivingSuffixes_card_mul_le (B : SimpleProperBlueprint)
    (H : ERSGraph L R B.C r t) (p : Fin B.P) (K : IndexTuple B t)
    (z : Formal.Streaming.Edge (Left B L) (Right B R))
    (hz : z ∈ edgesAt B H p K) :
    (survivingSuffixes B H p K z).card * t ≤
      B.P * Fintype.card (SuffixIndexTuple B t p) := by
  classical
  let target : SuffixCoordinates B p → Fin t := fun q ↦ K q.1
  have hsubset : survivingSuffixes B H p K z ⊆ coordinateHits target := by
    intro S hS
    have hspecial : IsSpecial B H (completeWithSuffix p K S) z :=
      (mem_survivingSuffixes_iff B H p K z S).1 hS
    obtain ⟨q, hpq, hq⟩ := special_edge_index_witness B H
      (completeWithSuffix p K S) (agreeBefore_completeWithSuffix p K S) hz hspecial
    rw [mem_coordinateHits_iff]
    refine ⟨⟨q, hpq⟩, ?_⟩
    change S ⟨q, hpq⟩ = K q
    simpa [completeWithSuffix, hpq] using hq.symm
  have hhit := coordinateHits_card_mul_le target
  have hsuffixCard : Fintype.card (SuffixCoordinates B p) ≤ B.P := by
    simpa using (Fintype.card_subtype_le fun q : Fin B.P ↦ p ≤ q)
  calc
    (survivingSuffixes B H p K z).card * t ≤
        (coordinateHits target).card * t :=
      Nat.mul_le_mul_right t (Finset.card_le_card hsubset)
    _ ≤ Fintype.card (SuffixCoordinates B p) *
        Fintype.card (SuffixIndexTuple B t p) := hhit
    _ ≤ B.P * Fintype.card (SuffixIndexTuple B t p) :=
      Nat.mul_le_mul_right _ hsuffixCard

theorem suffixIndexTuple_card (B : SimpleProperBlueprint) (p : Fin B.P) :
    Fintype.card (SuffixIndexTuple B t p) =
      t ^ Fintype.card (SuffixCoordinates B p) := by
  classical
  simp [SuffixIndexTuple, Fintype.card_pi]

end SimpleExpansion

end Formal.Streaming
