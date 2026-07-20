import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

namespace Formal.Streaming

abbrev Edge (L R : Type*) := L × R

structure BipartiteGraph (L R : Type*) where
  edges : Finset (Edge L R)
deriving DecidableEq

namespace BipartiteGraph

variable {L R : Type*}

instance : Membership (Edge L R) (BipartiteGraph L R) :=
  ⟨fun e G => e ∈ G.edges⟩

@[ext]
theorem ext {G H : BipartiteGraph L R} (h : G.edges = H.edges) : G = H := by
  cases G
  cases H
  simp_all

def empty : BipartiteGraph L R := ⟨∅⟩

def union [DecidableEq L] [DecidableEq R]
    (G H : BipartiteGraph L R) : BipartiteGraph L R :=
  ⟨G.edges ∪ H.edges⟩

def IsMatching (G : BipartiteGraph L R) (M : Finset (Edge L R)) : Prop :=
  M ⊆ G.edges ∧
    (∀ ⦃e f : Edge L R⦄, e ∈ M → f ∈ M → e.1 = f.1 → e = f) ∧
    (∀ ⦃e f : Edge L R⦄, e ∈ M → f ∈ M → e.2 = f.2 → e = f)

theorem isMatching_iff {G : BipartiteGraph L R} {M : Finset (Edge L R)} :
    G.IsMatching M ↔
      M ⊆ G.edges ∧
        (∀ ⦃e f : Edge L R⦄, e ∈ M → f ∈ M → e.1 = f.1 → e = f) ∧
        (∀ ⦃e f : Edge L R⦄, e ∈ M → f ∈ M → e.2 = f.2 → e = f) :=
  Iff.rfl

@[simp]
theorem empty_isMatching (G : BipartiteGraph L R) : G.IsMatching ∅ := by
  simp [IsMatching]

theorem IsMatching.subset {G : BipartiteGraph L R}
    {M N : Finset (Edge L R)} (hM : G.IsMatching M) (hNM : N ⊆ M) :
    G.IsMatching N := by
  refine ⟨hNM.trans hM.1, ?_, ?_⟩
  · intro e f he hf hef
    exact hM.2.1 (hNM he) (hNM hf) hef
  · intro e f he hf hef
    exact hM.2.2 (hNM he) (hNM hf) hef

noncomputable def matchingNumber [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) : ℕ := by
  classical
  exact (Finset.univ.filter G.IsMatching).sup Finset.card

theorem matching_card_le [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) {M : Finset (Edge L R)}
    (hM : G.IsMatching M) : M.card ≤ G.matchingNumber := by
  classical
  unfold matchingNumber
  apply Finset.le_sup
  simp [hM]

theorem exists_maximum_matching [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) :
    ∃ M : Finset (Edge L R), G.IsMatching M ∧ M.card = G.matchingNumber := by
  classical
  let candidates := Finset.univ.filter G.IsMatching
  have hempty : (∅ : Finset (Edge L R)) ∈ candidates := by
    simp [candidates]
  obtain ⟨M, hMcand, hsup⟩ :=
    Finset.exists_mem_eq_sup candidates ⟨∅, hempty⟩ Finset.card
  refine ⟨M, ?_, ?_⟩
  · simpa [candidates] using hMcand
  · simpa [matchingNumber, candidates] using hsup.symm

def IsMaximumMatching [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (M : Finset (Edge L R)) : Prop :=
  G.IsMatching M ∧ M.card = G.matchingNumber

def IsEdgeStream [DecidableEq L] [DecidableEq R]
    (G : BipartiteGraph L R) (xs : List (Edge L R)) : Prop :=
  xs.Nodup ∧ xs.toFinset = G.edges

structure EdgeStream [DecidableEq L] [DecidableEq R]
    (G : BipartiteGraph L R) where
  order : List (Edge L R)
  nodup : order.Nodup
  covers : order.toFinset = G.edges

namespace EdgeStream

variable [DecidableEq L] [DecidableEq R]

@[simp]
theorem isEdgeStream (G : BipartiteGraph L R) (σ : EdgeStream G) :
    G.IsEdgeStream σ.order :=
  ⟨σ.nodup, σ.covers⟩

noncomputable def canonical (G : BipartiteGraph L R) : EdgeStream G where
  order := G.edges.toList
  nodup := G.edges.nodup_toList
  covers := G.edges.toList_toFinset

theorem perm (G : BipartiteGraph L R) (σ τ : EdgeStream G) :
    σ.order.Perm τ.order :=
  List.perm_of_nodup_nodup_toFinset_eq σ.nodup τ.nodup
    (σ.covers.trans τ.covers.symm)

@[simp]
theorem length_eq_card (G : BipartiteGraph L R) (σ : EdgeStream G) :
    σ.order.length = G.edges.card := by
  rw [← σ.covers, List.toFinset_card_of_nodup σ.nodup]

end EdgeStream

end BipartiteGraph

end Formal.Streaming
