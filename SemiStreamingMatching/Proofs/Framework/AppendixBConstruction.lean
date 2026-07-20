import SemiStreamingMatching.Proofs.Framework.ERSFamily
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

namespace AppendixBConstruction

abbrev Box (d p : ℕ) := Fin d → Fin p

def Fits {d p : ℕ} (S : Finset (Fin d)) (a : ℕ) (u : Box d p) : Prop :=
  ∀ k, k ∈ S → (u k).val + a < p

def translate {d p : ℕ} (S : Finset (Fin d)) (a : ℕ) (u : Box d p)
    (h : Fits S a u) : Box d p :=
  fun k ↦ if hk : k ∈ S then ⟨(u k).val + a, h k hk⟩ else u k

noncomputable def translate? {d p : ℕ} (S : Finset (Fin d)) (a : ℕ)
    (u : Box d p) : Option (Box d p) := by
  classical
  exact if h : Fits S a u then some (translate S a u h) else none

theorem translate?_eq_some_iff {d p : ℕ} {S : Finset (Fin d)} {a : ℕ}
    {u v : Box d p} :
    translate? S a u = some v ↔ ∃ h : Fits S a u, translate S a u h = v := by
  classical
  unfold translate?
  split <;> rename_i h
  · simp only [Option.some.injEq]
    exact ⟨fun huv ↦ ⟨h, huv⟩, fun hex ↦ hex.choose_spec⟩
  · simp [h]

@[simp]
theorem translate_apply_mem {d p : ℕ} {S : Finset (Fin d)} {a : ℕ}
    {u : Box d p} (h : Fits S a u) {k : Fin d} (hk : k ∈ S) :
    ((translate S a u h) k).val = (u k).val + a := by
  simp [translate, hk]

@[simp]
theorem translate_apply_not_mem {d p : ℕ} {S : Finset (Fin d)} {a : ℕ}
    {u : Box d p} (h : Fits S a u) {k : Fin d} (hk : k ∉ S) :
    (translate S a u h) k = u k := by
  simp [translate, hk]

theorem translate?_left_injective {d p : ℕ} {S : Finset (Fin d)} {a : ℕ}
    {u u' v : Box d p}
    (hu : translate? S a u = some v)
    (hu' : translate? S a u' = some v) : u = u' := by
  classical
  rw [translate?_eq_some_iff] at hu hu'
  obtain ⟨h, rfl⟩ := hu
  obtain ⟨h', hv⟩ := hu'
  funext k
  by_cases hk : k ∈ S
  · have hval := congrArg (fun z : Box d p ↦ (z k).val) hv
    simp only [translate_apply_mem h hk, translate_apply_mem h' hk] at hval
    exact Fin.ext (Nat.add_right_cancel hval.symm)
  · have hk' := congrArg (fun z : Box d p ↦ z k) hv
    simpa [translate_apply_not_mem h hk, translate_apply_not_mem h' hk] using hk'.symm

def changedCoordinates {d p : ℕ} (u v : Box d p) : Finset (Fin d) :=
  Finset.univ.filter fun k ↦ u k ≠ v k

theorem changedCoordinates_eq_support {d p : ℕ} {S : Finset (Fin d)}
    {a : ℕ} (ha : 0 < a) {u v : Box d p}
    (huv : translate? S a u = some v) :
    changedCoordinates u v = S := by
  classical
  rw [translate?_eq_some_iff] at huv
  obtain ⟨h, rfl⟩ := huv
  ext k
  by_cases hk : k ∈ S
  · simp only [changedCoordinates, Finset.mem_filter, Finset.mem_univ, true_and, hk]
    constructor
    · intro
      trivial
    · intro
      apply ne_of_apply_ne Fin.val
      simp only [translate_apply_mem h hk]
      omega
  · simp [changedCoordinates, hk, translate_apply_not_mem h hk]

structure BoxConstructionData (C : ℕ) where
  d : ℕ
  p : ℕ
  r : ℕ
  t : ℕ
  supportWeight : ℕ
  intersectionCap : ℕ
  C_pos : 0 < C
  p_pos : 0 < p
  r_pos : 0 < r
  t_pos : 0 < t
  supports : Fin t → Finset (Fin d)
  support_card : ∀ i, (supports i).card = supportWeight
  intersection_lt_support : intersectionCap < supportWeight
  support_intersection : ∀ {i j}, i ≠ j →
    ((supports i) ∩ (supports j)).card ≤ intersectionCap

  color : Fin t → Box d p → Option (Fin C)

  shift : Fin C → Fin C → ℕ
  shift_pos : ∀ x y, 0 < shift x y

  cross_color : ∀ {i j : Fin t} {x y a b : Fin C} {u v : Box d p},
    i ≠ j →
    color i u = some a → color i v = some b →
    translate? (supports j) (shift x y) u = some v → a = b

  fiber_card : ∀ i x y,
    r ≤ (Finset.univ.filter fun e :
      Edge (Fin (Fintype.card (Box d p))) (Fin (Fintype.card (Box d p))) ↦
        color i ((Fintype.equivFin (Box d p)).symm e.1) = some x ∧
        color i ((Fintype.equivFin (Box d p)).symm e.2) = some y ∧
        translate? (supports i) (shift x y)
          ((Fintype.equivFin (Box d p)).symm e.1) =
            some ((Fintype.equivFin (Box d p)).symm e.2)).card

namespace BoxConstructionData

variable {C : ℕ}

def n (D : BoxConstructionData C) : ℕ := Fintype.card (Box D.d D.p)

theorem n_eq_pow (D : BoxConstructionData C) : D.n = D.p ^ D.d := by
  simp [n, Box]

noncomputable def decode (D : BoxConstructionData C) : Fin D.n → Box D.d D.p :=
  (Fintype.equivFin (Box D.d D.p)).symm

theorem decode_injective (D : BoxConstructionData C) : Function.Injective D.decode :=
  (Fintype.equivFin (Box D.d D.p)).symm.injective

noncomputable def rawMatching (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) : Finset (Edge (Fin D.n) (Fin D.n)) :=
  Finset.univ.filter fun e ↦
    D.color i (D.decode e.1) = some x ∧
    D.color i (D.decode e.2) = some y ∧
    translate? (D.supports i) (D.shift x y) (D.decode e.1) = some (D.decode e.2)

@[simp]
theorem mem_rawMatching_iff (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) (e : Edge (Fin D.n) (Fin D.n)) :
    e ∈ D.rawMatching i x y ↔
      D.color i (D.decode e.1) = some x ∧
      D.color i (D.decode e.2) = some y ∧
      translate? (D.supports i) (D.shift x y) (D.decode e.1) = some (D.decode e.2) := by
  simp [rawMatching]

theorem rawMatching_card (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) : D.r ≤ (D.rawMatching i x y).card := by
  simpa [rawMatching, decode, n] using D.fiber_card i x y

theorem supports_injective (D : BoxConstructionData C) :
    Function.Injective D.supports := by
  intro i j hij
  by_contra hne
  have hinter := D.support_intersection hne
  have heq : (D.supports i ∩ D.supports j).card = D.supportWeight := by
    rw [hij, Finset.inter_self, D.support_card]
  have hle : D.supportWeight ≤ D.intersectionCap := heq ▸ hinter
  exact (not_le_of_gt D.intersection_lt_support) hle

theorem rawMatching_left_unique (D : BoxConstructionData C)
    {i : Fin D.t} {x y : Fin C} {e f : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ D.rawMatching i x y) (hf : f ∈ D.rawMatching i x y)
    (hleft : e.1 = f.1) : e = f := by
  rw [D.mem_rawMatching_iff] at he hf
  rcases he with ⟨-, -, he⟩
  rcases hf with ⟨-, -, hf⟩
  have hrightDecoded : D.decode e.2 = D.decode f.2 := by
    rw [← hleft] at hf
    exact Option.some.inj (he.symm.trans hf)
  have hright : e.2 = f.2 := D.decode_injective hrightDecoded
  exact Prod.ext hleft hright

theorem rawMatching_right_unique (D : BoxConstructionData C)
    {i : Fin D.t} {x y : Fin C} {e f : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ D.rawMatching i x y) (hf : f ∈ D.rawMatching i x y)
    (hright : e.2 = f.2) : e = f := by
  rw [D.mem_rawMatching_iff] at he hf
  rcases he with ⟨-, -, he⟩
  rcases hf with ⟨-, -, hf⟩
  have hleftDecoded : D.decode e.1 = D.decode f.1 :=
    translate?_left_injective he (by simpa [hright] using hf)
  have hleft : e.1 = f.1 := D.decode_injective hleftDecoded
  exact Prod.ext hleft hright

theorem raw_matching_groups_disjoint (D : BoxConstructionData C)
    {i j : Fin D.t} (hij : i ≠ j) :
    Disjoint (ERSGraph.matchingGroupOf D.rawMatching i)
      (ERSGraph.matchingGroupOf D.rawMatching j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at hei hej
  obtain ⟨x, y, hei⟩ := hei
  obtain ⟨x', y', hej⟩ := hej
  rw [D.mem_rawMatching_iff] at hei hej
  have hiChanged := changedCoordinates_eq_support (D.shift_pos x y) hei.2.2
  have hjChanged := changedCoordinates_eq_support (D.shift_pos x' y') hej.2.2
  have hsupp : D.supports i = D.supports j := hiChanged.symm.trans hjChanged
  exact hij (D.supports_injective hsupp)

noncomputable def trimTo {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (r : ℕ) (h : r ≤ s.card) : Finset alpha :=
  Classical.choose (Finset.le_card_iff_exists_subset_card.mp h)

theorem trimTo_subset {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (r : ℕ) (h : r ≤ s.card) : trimTo s r h ⊆ s :=
  (Classical.choose_spec (Finset.le_card_iff_exists_subset_card.mp h)).1

theorem trimTo_card {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (r : ℕ) (h : r ≤ s.card) : (trimTo s r h).card = r :=
  (Classical.choose_spec (Finset.le_card_iff_exists_subset_card.mp h)).2

noncomputable def matching (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) : Finset (Edge (Fin D.n) (Fin D.n)) :=
  trimTo (D.rawMatching i x y) D.r (D.rawMatching_card i x y)

theorem matching_subset_raw (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) :
    D.matching i x y ⊆ D.rawMatching i x y :=
  trimTo_subset _ _ _

@[simp]
theorem matching_card (D : BoxConstructionData C)
    (i : Fin D.t) (x y : Fin C) : (D.matching i x y).card = D.r :=
  trimTo_card _ _ _

noncomputable def leftGroup (D : BoxConstructionData C)
    (i : Fin D.t) (x : Fin C) : Finset (Fin D.n) :=
  (ERSGraph.leftVertices (ERSGraph.matchingGroupOf D.matching i)).filter
    fun u ↦ D.color i (D.decode u) = some x

noncomputable def rightGroup (D : BoxConstructionData C)
    (i : Fin D.t) (x : Fin C) : Finset (Fin D.n) :=
  (ERSGraph.rightVertices (ERSGraph.matchingGroupOf D.matching i)).filter
    fun v ↦ D.color i (D.decode v) = some x

private theorem matching_mem_group (D : BoxConstructionData C)
    {i : Fin D.t} {x y : Fin C} {e : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ D.matching i x y) :
    e ∈ ERSGraph.matchingGroupOf D.matching i := by
  simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨x, y, he⟩

private theorem matching_colors (D : BoxConstructionData C)
    {i : Fin D.t} {x y : Fin C} {e : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ D.matching i x y) :
    D.color i (D.decode e.1) = some x ∧
      D.color i (D.decode e.2) = some y := by
  have hraw := (D.mem_rawMatching_iff _ _ _ _).mp (D.matching_subset_raw i x y he)
  exact ⟨hraw.1, hraw.2.1⟩

theorem matching_between (D : BoxConstructionData C)
    {i : Fin D.t} {x y : Fin C} {e : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ D.matching i x y) :
    e.1 ∈ D.leftGroup i x ∧ e.2 ∈ D.rightGroup i y := by
  have heGroup := D.matching_mem_group he
  have hcolors := D.matching_colors he
  constructor
  · simp only [leftGroup, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨e, heGroup, rfl⟩, hcolors.1⟩
  · simp only [rightGroup, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨e, heGroup, rfl⟩, hcolors.2⟩

theorem left_groups_disjoint (D : BoxConstructionData C)
    (i : Fin D.t) {x y : Fin C} (hxy : x ≠ y) :
    Disjoint (D.leftGroup i x) (D.leftGroup i y) := by
  rw [Finset.disjoint_left]
  intro u hux huy
  simp only [leftGroup, Finset.mem_filter] at hux huy
  exact hxy (Option.some.inj (hux.2.symm.trans huy.2))

theorem right_groups_disjoint (D : BoxConstructionData C)
    (i : Fin D.t) {x y : Fin C} (hxy : x ≠ y) :
    Disjoint (D.rightGroup i x) (D.rightGroup i y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  simp only [rightGroup, Finset.mem_filter] at hvx hvy
  exact hxy (Option.some.inj (hvx.2.symm.trans hvy.2))

private theorem left_endpoint_has_color (D : BoxConstructionData C)
    {i : Fin D.t} {u : Fin D.n}
    (hu : u ∈ ERSGraph.leftVertices (ERSGraph.matchingGroupOf D.matching i)) :
    ∃ x, D.color i (D.decode u) = some x := by
  rw [ERSGraph.leftVertices, Finset.mem_image] at hu
  obtain ⟨e, heGroup, heLeft⟩ := hu
  simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at heGroup
  obtain ⟨x, y, he⟩ := heGroup
  refine ⟨x, ?_⟩
  simpa [← heLeft] using (D.matching_colors he).1

private theorem right_endpoint_has_color (D : BoxConstructionData C)
    {i : Fin D.t} {v : Fin D.n}
    (hv : v ∈ ERSGraph.rightVertices (ERSGraph.matchingGroupOf D.matching i)) :
    ∃ y, D.color i (D.decode v) = some y := by
  rw [ERSGraph.rightVertices, Finset.mem_image] at hv
  obtain ⟨e, heGroup, heRight⟩ := hv
  simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at heGroup
  obtain ⟨x, y, he⟩ := heGroup
  refine ⟨y, ?_⟩
  simpa [← heRight] using (D.matching_colors he).2

theorem left_decomposition (D : BoxConstructionData C) (i : Fin D.t) :
    ERSGraph.leftVertices (ERSGraph.matchingGroupOf D.matching i) =
      ERSGraph.vertexGroupUnion (D.leftGroup i) := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hx⟩ := D.left_endpoint_has_color hu
    simp only [ERSGraph.vertexGroupUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨x, Finset.mem_filter.mpr ⟨hu, hx⟩⟩
  · intro hu
    simp only [ERSGraph.vertexGroupUnion, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, hx⟩ := hu
    exact (Finset.mem_filter.mp hx).1

theorem right_decomposition (D : BoxConstructionData C) (i : Fin D.t) :
    ERSGraph.rightVertices (ERSGraph.matchingGroupOf D.matching i) =
      ERSGraph.vertexGroupUnion (D.rightGroup i) := by
  ext v
  constructor
  · intro hv
    obtain ⟨y, hy⟩ := D.right_endpoint_has_color hv
    simp only [ERSGraph.vertexGroupUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨y, Finset.mem_filter.mpr ⟨hv, hy⟩⟩
  · intro hv
    simp only [ERSGraph.vertexGroupUnion, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hv
    obtain ⟨y, hy⟩ := hv
    exact (Finset.mem_filter.mp hy).1

theorem matching_groups_disjoint (D : BoxConstructionData C)
    {i j : Fin D.t} (hij : i ≠ j) :
    Disjoint (ERSGraph.matchingGroupOf D.matching i)
      (ERSGraph.matchingGroupOf D.matching j) := by
  apply (D.raw_matching_groups_disjoint hij).mono
  · intro e he
    simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at he ⊢
    obtain ⟨x, y, he⟩ := he
    exact ⟨x, y, D.matching_subset_raw i x y he⟩
  · intro e he
    simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at he ⊢
    obtain ⟨x, y, he⟩ := he
    exact ⟨x, y, D.matching_subset_raw j x y he⟩

theorem cross_induced (D : BoxConstructionData C)
    {i j : Fin D.t} (hij : i ≠ j)
    {e : Edge (Fin D.n) (Fin D.n)}
    (he : e ∈ ERSGraph.matchingGroupOf D.matching j)
    (hl : e.1 ∈ ERSGraph.leftVertices (ERSGraph.matchingGroupOf D.matching i))
    (hr : e.2 ∈ ERSGraph.rightVertices (ERSGraph.matchingGroupOf D.matching i)) :
    ∃ x, e.1 ∈ D.leftGroup i x ∧ e.2 ∈ D.rightGroup i x := by
  obtain ⟨a, ha⟩ := D.left_endpoint_has_color hl
  obtain ⟨b, hb⟩ := D.right_endpoint_has_color hr
  simp only [ERSGraph.matchingGroupOf, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at he
  obtain ⟨x, y, he⟩ := he
  have heRaw := (D.mem_rawMatching_iff _ _ _ _).mp (D.matching_subset_raw j x y he)
  have hab : a = b := D.cross_color hij ha hb heRaw.2.2
  refine ⟨a, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hl, ha⟩
  · exact Finset.mem_filter.mpr ⟨hr, hab ▸ hb⟩

noncomputable def toAppendixBFiniteData (D : BoxConstructionData C) :
    AppendixBFiniteData C where
  n := D.n
  r := D.r
  t := D.t
  d := D.d
  supportWeight := D.supportWeight
  intersectionCap := D.intersectionCap
  C_pos := D.C_pos
  r_pos := D.r_pos
  t_pos := D.t_pos
  supports := D.supports
  support_card := D.support_card
  intersection_lt_support := D.intersection_lt_support
  support_intersection := D.support_intersection
  matching := D.matching
  leftGroup := D.leftGroup
  rightGroup := D.rightGroup
  matching_card := D.matching_card
  matching_left_unique := by
    intro i x y e f he hf hleft
    exact D.rawMatching_left_unique
      (D.matching_subset_raw i x y he) (D.matching_subset_raw i x y hf) hleft
  matching_right_unique := by
    intro i x y e f he hf hright
    exact D.rawMatching_right_unique
      (D.matching_subset_raw i x y he) (D.matching_subset_raw i x y hf) hright
  matching_between := D.matching_between
  left_groups_disjoint := D.left_groups_disjoint
  right_groups_disjoint := D.right_groups_disjoint
  left_decomposition := D.left_decomposition
  right_decomposition := D.right_decomposition
  matching_groups_disjoint := D.matching_groups_disjoint
  cross_induced := D.cross_induced

@[simp]
theorem toAppendixBFiniteData_n (D : BoxConstructionData C) :
    D.toAppendixBFiniteData.n = D.p ^ D.d := by
  exact D.n_eq_pow

end BoxConstructionData

end AppendixBConstruction

end ERSFamily

end Formal.Streaming
