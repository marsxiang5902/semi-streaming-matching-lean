import SemiStreamingMatching.Definitions.Graph

namespace Formal.Streaming

namespace BipartiteGraph

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

def leftEndpoints (M : Finset (Edge L R)) : Finset L := M.image Prod.fst

def rightEndpoints (M : Finset (Edge L R)) : Finset R := M.image Prod.snd

@[simp]
theorem mem_leftEndpoints_iff {M : Finset (Edge L R)} {l : L} :
    l ∈ leftEndpoints M ↔ ∃ r, (l, r) ∈ M := by
  simp [leftEndpoints]

@[simp]
theorem mem_rightEndpoints_iff {M : Finset (Edge L R)} {r : R} :
    r ∈ rightEndpoints M ↔ ∃ l, (l, r) ∈ M := by
  simp [rightEndpoints]

theorem leftEndpoints_card_of_isMatching
    {G : BipartiteGraph L R} {M : Finset (Edge L R)} (hM : G.IsMatching M) :
    (leftEndpoints M).card = M.card := by
  classical
  rw [leftEndpoints, Finset.card_image_iff]
  intro e he f hf hleft
  exact hM.2.1 he hf hleft

theorem rightEndpoints_card_of_isMatching
    {G : BipartiteGraph L R} {M : Finset (Edge L R)} (hM : G.IsMatching M) :
    (rightEndpoints M).card = M.card := by
  classical
  rw [rightEndpoints, Finset.card_image_iff]
  intro e he f hf hright
  exact hM.2.2 he hf hright

theorem card_not_leftEndpoint_of_isMatching
    {G : BipartiteGraph L R} {M : Finset (Edge L R)} (hM : G.IsMatching M) :
    (Finset.univ.filter fun l ↦ l ∉ leftEndpoints M).card =
      Fintype.card L - M.card := by
  have hset : (Finset.univ.filter fun l ↦ l ∉ leftEndpoints M) =
      Finset.univ \ leftEndpoints M := by
    ext l
    simp
  rw [hset, Finset.card_sdiff (Finset.subset_univ _),
    Finset.card_univ, leftEndpoints_card_of_isMatching hM]

theorem card_not_rightEndpoint_of_isMatching
    {G : BipartiteGraph L R} {M : Finset (Edge L R)} (hM : G.IsMatching M) :
    (Finset.univ.filter fun r ↦ r ∉ rightEndpoints M).card =
      Fintype.card R - M.card := by
  have hset : (Finset.univ.filter fun r ↦ r ∉ rightEndpoints M) =
      Finset.univ \ rightEndpoints M := by
    ext r
    simp
  rw [hset, Finset.card_sdiff (Finset.subset_univ _),
    Finset.card_univ, rightEndpoints_card_of_isMatching hM]

def IsVertexCover (G : BipartiteGraph L R) (CL : Finset L) (CR : Finset R) : Prop :=
  ∀ ⦃e : Edge L R⦄, e ∈ G.edges → e.1 ∈ CL ∨ e.2 ∈ CR

theorem matching_card_le_vertexCover
    {G : BipartiteGraph L R} {M : Finset (Edge L R)}
    (hM : G.IsMatching M) {CL : Finset L} {CR : Finset R}
    (hcover : G.IsVertexCover CL CR) :
    M.card ≤ CL.card + CR.card := by
  classical
  let assign : {e // e ∈ M} → Sum {l // l ∈ CL} {r // r ∈ CR} := fun e ↦
    if hl : e.1.1 ∈ CL then Sum.inl ⟨e.1.1, hl⟩
    else Sum.inr ⟨e.1.2, (hcover (hM.1 e.2)).resolve_left hl⟩
  have hinj : Function.Injective assign := by
    intro e f hef
    by_cases heL : e.1.1 ∈ CL
    · have heassign : assign e = Sum.inl ⟨e.1.1, heL⟩ := by simp [assign, heL]
      rw [heassign] at hef
      by_cases hfL : f.1.1 ∈ CL
      · have hfassign : assign f = Sum.inl ⟨f.1.1, hfL⟩ := by simp [assign, hfL]
        rw [hfassign] at hef
        have hleft : e.1.1 = f.1.1 := congrArg (fun z ↦ Sum.elim Subtype.val
          (fun _ : {r // r ∈ CR} ↦ e.1.1) z) hef
        apply Subtype.ext
        exact hM.2.1 e.2 f.2 hleft
      · simp [assign, hfL] at hef
    · have heassign : assign e = Sum.inr
          ⟨e.1.2, (hcover (hM.1 e.2)).resolve_left heL⟩ := by simp [assign, heL]
      rw [heassign] at hef
      by_cases hfL : f.1.1 ∈ CL
      · simp [assign, hfL] at hef
      · have hfassign : assign f = Sum.inr
            ⟨f.1.2, (hcover (hM.1 f.2)).resolve_left hfL⟩ := by simp [assign, hfL]
        rw [hfassign] at hef
        have hright : e.1.2 = f.1.2 := congrArg (fun z ↦ Sum.elim
          (fun _ : {l // l ∈ CL} ↦ e.1.2) Subtype.val z) hef
        apply Subtype.ext
        exact hM.2.2 e.2 f.2 hright
  have hcard := Fintype.card_le_of_injective assign hinj
  simpa using hcard

end BipartiteGraph

end Formal.Streaming
