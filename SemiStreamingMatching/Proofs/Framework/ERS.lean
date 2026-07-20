import SemiStreamingMatching.Proofs.Blueprint.Blueprint
import SemiStreamingMatching.Definitions.Graph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSGraph

variable {L R : Type*} {C r t : ℕ}

def matchingGroupOf [DecidableEq L] [DecidableEq R]
    (M : Fin t → Fin C → Fin C → Finset (Formal.Streaming.Edge L R))
    (i : Fin t) : Finset (Formal.Streaming.Edge L R) :=
  Finset.univ.biUnion fun x ↦ Finset.univ.biUnion fun y ↦ M i x y

def leftVertices [DecidableEq L] (M : Finset (Formal.Streaming.Edge L R)) : Finset L :=
  M.image Prod.fst

def rightVertices [DecidableEq R] (M : Finset (Formal.Streaming.Edge L R)) : Finset R :=
  M.image Prod.snd

def vertexGroupUnion {V : Type*} [DecidableEq V]
    (A : Fin C → Finset V) : Finset V :=
  Finset.univ.biUnion A

end ERSGraph

structure ERSGraph (L R : Type*) [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (C r t : ℕ) where
  graph : BipartiteGraph L R
  matching : Fin t → Fin C → Fin C → Finset (Formal.Streaming.Edge L R)
  leftGroup : Fin t → Fin C → Finset L
  rightGroup : Fin t → Fin C → Finset R
  C_pos : 0 < C
  r_pos : 0 < r
  t_pos : 0 < t
  side_card_eq : Fintype.card L = Fintype.card R
  matching_isMatching :
    ∀ i x y, graph.IsMatching (matching i x y)
  matching_card :
    ∀ i x y, (matching i x y).card = r
  matching_groups_disjoint :
    ∀ {i j : Fin t}, i ≠ j →
      Disjoint (ERSGraph.matchingGroupOf matching i)
        (ERSGraph.matchingGroupOf matching j)
  left_groups_disjoint :
    ∀ i {x y : Fin C}, x ≠ y → Disjoint (leftGroup i x) (leftGroup i y)
  right_groups_disjoint :
    ∀ i {x y : Fin C}, x ≠ y → Disjoint (rightGroup i x) (rightGroup i y)
  matching_between :
    ∀ {i x y} {e : Formal.Streaming.Edge L R}, e ∈ matching i x y →
      e.1 ∈ leftGroup i x ∧ e.2 ∈ rightGroup i y
  left_decomposition :
    ∀ i, ERSGraph.leftVertices (ERSGraph.matchingGroupOf matching i) =
      ERSGraph.vertexGroupUnion (leftGroup i)
  right_decomposition :
    ∀ i, ERSGraph.rightVertices (ERSGraph.matchingGroupOf matching i) =
      ERSGraph.vertexGroupUnion (rightGroup i)
  inducedness :
    ∀ {i} {e : Formal.Streaming.Edge L R},
      e ∈ graph.edges →
      e ∉ ERSGraph.matchingGroupOf matching i →
      e.1 ∈ ERSGraph.leftVertices (ERSGraph.matchingGroupOf matching i) →
      e.2 ∈ ERSGraph.rightVertices (ERSGraph.matchingGroupOf matching i) →
      ∃ x, e.1 ∈ leftGroup i x ∧ e.2 ∈ rightGroup i x

namespace ERSGraph

variable {L R : Type*} {C r t : ℕ}
variable [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def matchingGroup (H : ERSGraph L R C r t) (i : Fin t) :
    Finset (Formal.Streaming.Edge L R) :=
  matchingGroupOf H.matching i

@[simp]
theorem mem_matchingGroup_iff (H : ERSGraph L R C r t)
    (i : Fin t) (e : Formal.Streaming.Edge L R) :
    e ∈ H.matchingGroup i ↔ ∃ x y, e ∈ H.matching i x y := by
  simp [matchingGroup, matchingGroupOf]

theorem matching_subset_graph (H : ERSGraph L R C r t) (i : Fin t)
    (x y : Fin C) : H.matching i x y ⊆ H.graph.edges :=
  (H.matching_isMatching i x y).1

theorem matchingGroup_subset_graph (H : ERSGraph L R C r t) (i : Fin t) :
    H.matchingGroup i ⊆ H.graph.edges := by
  intro e he
  rw [H.mem_matchingGroup_iff] at he
  obtain ⟨x, y, he⟩ := he
  exact H.matching_subset_graph i x y he

theorem matchingGroup_disjoint (H : ERSGraph L R C r t)
    {i j : Fin t} (hij : i ≠ j) :
    Disjoint (H.matchingGroup i) (H.matchingGroup j) :=
  H.matching_groups_disjoint hij

theorem edge_mem_groups (H : ERSGraph L R C r t)
    {i : Fin t} {x y : Fin C} {e : Formal.Streaming.Edge L R}
    (he : e ∈ H.matching i x y) :
    e.1 ∈ H.leftGroup i x ∧ e.2 ∈ H.rightGroup i y :=
  H.matching_between he

theorem left_group_index_unique (H : ERSGraph L R C r t)
    {i : Fin t} {x y : Fin C} {l : L}
    (hx : l ∈ H.leftGroup i x) (hy : l ∈ H.leftGroup i y) : x = y := by
  by_contra hxy
  exact Finset.disjoint_left.mp (H.left_groups_disjoint i hxy) hx hy

theorem right_group_index_unique (H : ERSGraph L R C r t)
    {i : Fin t} {x y : Fin C} {v : R}
    (hx : v ∈ H.rightGroup i x) (hy : v ∈ H.rightGroup i y) : x = y := by
  by_contra hxy
  exact Finset.disjoint_left.mp (H.right_groups_disjoint i hxy) hx hy

theorem left_label_eq_of_endpoint_eq (H : ERSGraph L R C r t)
    {i : Fin t} {x y x' y' : Fin C}
    {e f : Formal.Streaming.Edge L R}
    (he : e ∈ H.matching i x y) (hf : f ∈ H.matching i x' y')
    (hleft : e.1 = f.1) : x = x' := by
  apply H.left_group_index_unique (H.edge_mem_groups he).1
  simpa [hleft] using (H.edge_mem_groups hf).1

theorem right_label_eq_of_endpoint_eq (H : ERSGraph L R C r t)
    {i : Fin t} {x y x' y' : Fin C}
    {e f : Formal.Streaming.Edge L R}
    (he : e ∈ H.matching i x y) (hf : f ∈ H.matching i x' y')
    (hright : e.2 = f.2) : y = y' := by
  apply H.right_group_index_unique (H.edge_mem_groups he).2
  simpa [hright] using (H.edge_mem_groups hf).2

theorem labelled_matchings_disjoint (H : ERSGraph L R C r t)
    {i : Fin t} {x y x' y' : Fin C}
    (hne : (x, y) ≠ (x', y')) :
    Disjoint (H.matching i x y) (H.matching i x' y') := by
  rw [Finset.disjoint_left]
  intro e he he'
  have hx : x = x' := H.left_label_eq_of_endpoint_eq he he' rfl
  have hy : y = y' := H.right_label_eq_of_endpoint_eq he he' rfl
  exact hne (by simp [hx, hy])

theorem not_mem_matchingGroup_of_mem_of_ne (H : ERSGraph L R C r t)
    {i j : Fin t} (hij : i ≠ j) {e : Formal.Streaming.Edge L R}
    (he : e ∈ H.matchingGroup i) : e ∉ H.matchingGroup j := by
  intro hej
  exact Finset.disjoint_left.mp (H.matchingGroup_disjoint hij) he hej

theorem leftGroup_subset_vertices (H : ERSGraph L R C r t)
    (i : Fin t) (x : Fin C) :
    H.leftGroup i x ⊆ leftVertices (H.matchingGroup i) := by
  intro l hl
  change l ∈ leftVertices (matchingGroupOf H.matching i)
  rw [H.left_decomposition i]
  simpa [vertexGroupUnion] using (show ∃ a, l ∈ H.leftGroup i a from ⟨x, hl⟩)

theorem rightGroup_subset_vertices (H : ERSGraph L R C r t)
    (i : Fin t) (x : Fin C) :
    H.rightGroup i x ⊆ rightVertices (H.matchingGroup i) := by
  intro v hv
  change v ∈ rightVertices (matchingGroupOf H.matching i)
  rw [H.right_decomposition i]
  simpa [vertexGroupUnion] using (show ∃ a, v ∈ H.rightGroup i a from ⟨x, hv⟩)

theorem induced_same_label (H : ERSGraph L R C r t)
    {i j : Fin t} (hij : i ≠ j) {x y : Fin C}
    {e : Formal.Streaming.Edge L R}
    (he : e ∈ H.matchingGroup i)
    (hl : e.1 ∈ H.leftGroup j x)
    (hr : e.2 ∈ H.rightGroup j y) : x = y := by
  have heG : e ∈ H.graph.edges := H.matchingGroup_subset_graph i he
  have hnot : e ∉ H.matchingGroup j :=
    H.not_mem_matchingGroup_of_mem_of_ne hij he
  obtain ⟨z, hlz, hrz⟩ := H.inducedness heG hnot
    (H.leftGroup_subset_vertices j x hl)
    (H.rightGroup_subset_vertices j y hr)
  exact (H.left_group_index_unique hl hlz).trans
    (H.right_group_index_unique hr hrz).symm

end ERSGraph

end Formal.Streaming
