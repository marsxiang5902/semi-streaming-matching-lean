import SemiStreamingMatching.Definitions.Graph

namespace Formal.Streaming

namespace BipartiteGraph

variable {L R L' R' : Type*}
  [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
  [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

def relabelEdge (eL : L ≃ L') (eR : R ≃ R') (e : Edge L R) : Edge L' R' :=
  (eL e.1, eR e.2)

def relabelEdges (eL : L ≃ L') (eR : R ≃ R')
    (E : Finset (Edge L R)) : Finset (Edge L' R') :=
  E.image (relabelEdge eL eR)

def relabel (G : BipartiteGraph L R) (eL : L ≃ L') (eR : R ≃ R') :
    BipartiteGraph L' R' :=
  ⟨relabelEdges eL eR G.edges⟩

theorem relabelEdge_injective (eL : L ≃ L') (eR : R ≃ R') :
    Function.Injective (relabelEdge eL eR) := by
  intro e f hef
  apply Prod.ext
  · exact eL.injective (congrArg Prod.fst hef)
  · exact eR.injective (congrArg Prod.snd hef)

@[simp]
theorem mem_relabelEdges_iff (eL : L ≃ L') (eR : R ≃ R')
    {E : Finset (Edge L R)} {z : Edge L' R'} :
    z ∈ relabelEdges eL eR E ↔ (eL.symm z.1, eR.symm z.2) ∈ E := by
  constructor
  · rw [relabelEdges, Finset.mem_image]
    rintro ⟨e, he, rfl⟩
    simpa [relabelEdge] using he
  · intro hz
    rw [relabelEdges, Finset.mem_image]
    refine ⟨(eL.symm z.1, eR.symm z.2), hz, ?_⟩
    simp [relabelEdge]

theorem relabelEdges_card (eL : L ≃ L') (eR : R ≃ R')
    (E : Finset (Edge L R)) :
    (relabelEdges eL eR E).card = E.card := by
  rw [relabelEdges, Finset.card_image_iff]
  intro e _ f _ hef
  exact relabelEdge_injective eL eR hef

theorem IsMatching.relabel {G : BipartiteGraph L R} {M : Finset (Edge L R)}
    (hM : G.IsMatching M) (eL : L ≃ L') (eR : R ≃ R') :
    (G.relabel eL eR).IsMatching (relabelEdges eL eR M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [mem_relabelEdges_iff] at hz
    exact (mem_relabelEdges_iff eL eR).2 (hM.1 hz)
  · intro z w hz hw hleft
    rw [relabelEdges, Finset.mem_image] at hz hw
    obtain ⟨e, he, rfl⟩ := hz
    obtain ⟨f, hf, rfl⟩ := hw
    apply congrArg (relabelEdge eL eR)
    exact hM.2.1 he hf (eL.injective hleft)
  · intro z w hz hw hright
    rw [relabelEdges, Finset.mem_image] at hz hw
    obtain ⟨e, he, rfl⟩ := hz
    obtain ⟨f, hf, rfl⟩ := hw
    apply congrArg (relabelEdge eL eR)
    exact hM.2.2 he hf (eR.injective hright)

theorem matchingNumber_relabel (G : BipartiteGraph L R)
    (eL : L ≃ L') (eR : R ≃ R') :
    (G.relabel eL eR).matchingNumber = G.matchingNumber := by
  apply Nat.le_antisymm
  · obtain ⟨M, hM, hcard⟩ := (G.relabel eL eR).exists_maximum_matching
    have hback := hM.relabel eL.symm eR.symm
    have hbackGraph : (G.relabel eL eR).relabel eL.symm eR.symm = G := by
      apply BipartiteGraph.ext
      ext z
      simp [relabel]
    rw [hbackGraph] at hback
    have hle := G.matching_card_le hback
    rw [relabelEdges_card, hcard] at hle
    exact hle
  · obtain ⟨M, hM, hcard⟩ := G.exists_maximum_matching
    have hmap := hM.relabel eL eR
    have hle := (G.relabel eL eR).matching_card_le hmap
    rw [relabelEdges_card, hcard] at hle
    exact hle

def EdgeStream.relabel (G : BipartiteGraph L R) (σ : G.EdgeStream)
    (eL : L ≃ L') (eR : R ≃ R') : (G.relabel eL eR).EdgeStream where
  order := σ.order.map (relabelEdge eL eR)
  nodup := σ.nodup.map (relabelEdge_injective eL eR)
  covers := by
    ext z
    have hmem : ∀ e, e ∈ σ.order ↔ e ∈ G.edges := by
      intro e
      rw [← List.mem_toFinset, σ.covers]
    change z ∈ (σ.order.map (relabelEdge eL eR)).toFinset ↔
      z ∈ relabelEdges eL eR G.edges
    simp only [List.mem_toFinset, List.mem_map, relabelEdges, Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hmem e).1 he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, (hmem e).2 he, rfl⟩

end BipartiteGraph

end Formal.Streaming
