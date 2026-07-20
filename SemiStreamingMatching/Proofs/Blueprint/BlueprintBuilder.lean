import SemiStreamingMatching.Proofs.Blueprint.Blueprint

namespace SimpleProperBlueprint

section Builder

variable {P C : ℕ}

noncomputable def matchingEdgeFamily
    (L R : Finset (Vertex P C))
    (pair : {l // l ∈ L} ≃ {r // r ∈ R})
    (group : {l // l ∈ L} → Fin P) : EdgeFamily P C := by
  classical
  exact fun p =>
    (Finset.univ.filter fun l : {l // l ∈ L} => group l = p).image
      (fun l => (l.1, (pair l).1))

theorem mem_matchingEdgeFamily_iff
    (L R : Finset (Vertex P C))
    (pair : {l // l ∈ L} ≃ {r // r ∈ R})
    (group : {l // l ∈ L} → Fin P)
    (p : Fin P) (l r : Vertex P C) :
    (l, r) ∈ matchingEdgeFamily L R pair group p ↔
      ∃ hl : l ∈ L,
        group ⟨l, hl⟩ = p ∧ (pair ⟨l, hl⟩).1 = r := by
  classical
  simp only [matchingEdgeFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hpair⟩
    have hal : a.1 = l := congrArg Prod.fst hpair
    have hl : l ∈ L := by
      rw [← hal]
      exact a.2
    have halSub : a = (⟨l, hl⟩ : {l // l ∈ L}) := Subtype.ext hal
    refine ⟨hl, ?_, ?_⟩
    · simpa [halSub] using ha
    · have har : (pair a).1 = r := congrArg Prod.snd hpair
      simpa [halSub] using har
  · rintro ⟨hl, hgroup, hpair⟩
    refine ⟨⟨l, hl⟩, hgroup, ?_⟩
    simp [hpair]

theorem leftMatched_matchingEdgeFamily_iff
    (L R : Finset (Vertex P C))
    (pair : {l // l ∈ L} ≃ {r // r ∈ R})
    (group : {l // l ∈ L} → Fin P)
    (l : Vertex P C) :
    leftMatched (matchingEdgeFamily L R pair group) l ↔ l ∈ L := by
  classical
  constructor
  · rintro ⟨p, r, hpr⟩
    exact (mem_matchingEdgeFamily_iff L R pair group p l r).mp hpr |>.choose
  · intro hl
    refine ⟨group ⟨l, hl⟩, (pair ⟨l, hl⟩).1, ?_⟩
    exact (mem_matchingEdgeFamily_iff L R pair group _ _ _).mpr
      ⟨hl, rfl, rfl⟩

theorem rightMatched_matchingEdgeFamily_iff
    (L R : Finset (Vertex P C))
    (pair : {l // l ∈ L} ≃ {r // r ∈ R})
    (group : {l // l ∈ L} → Fin P)
    (r : Vertex P C) :
    rightMatched (matchingEdgeFamily L R pair group) r ↔ r ∈ R := by
  classical
  constructor
  · rintro ⟨p, l, hpl⟩
    obtain ⟨hl, _, hpair⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group p l r).mp hpl
    rw [← hpair]
    exact (pair ⟨l, hl⟩).2
  · intro hr
    let l := pair.symm ⟨r, hr⟩
    refine ⟨group l, l.1, ?_⟩
    apply (mem_matchingEdgeFamily_iff L R pair group _ _ _).mpr
    refine ⟨l.2, rfl, ?_⟩
    exact congrArg Subtype.val (pair.apply_symm_apply ⟨r, hr⟩)

noncomputable def ofFinsetMatching
    (hP : 0 < P) (hC : 0 < C)
    (L R : Finset (Vertex P C))
    (pair : {l // l ∈ L} ≃ {r // r ∈ R})
    (group : {l // l ∈ L} → Fin P)
    (ban : ∀ l : {l // l ∈ L}, ∀ x : Suffix P C (group l),
      patchVertex (group l) l.1 x ∉ L ∨
        patchVertex (group l) (pair l).1 x ∉ R) :
    SimpleProperBlueprint where
  P := P
  hP := hP
  C := C
  hC := hC
  E := matchingEdgeFamily L R pair group
  left_matching := by
    intro p q l r₁ r₂ hp hq
    obtain ⟨hl, hgp, hpair₁⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group p l r₁).mp hp
    obtain ⟨hl', hgq, hpair₂⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group q l r₂).mp hq
    have hsub : (⟨l, hl⟩ : {l // l ∈ L}) = ⟨l, hl'⟩ := Subtype.ext (by rfl)
    constructor
    · exact hgp.symm.trans ((congrArg group hsub).trans hgq)
    · exact hpair₁.symm.trans
        ((congrArg (fun a => (pair a).1) hsub).trans hpair₂)
  right_matching := by
    intro p q l₁ l₂ r hp hq
    obtain ⟨hl₁, hgp, hpair₁⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group p l₁ r).mp hp
    obtain ⟨hl₂, hgq, hpair₂⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group q l₂ r).mp hq
    have heq : pair ⟨l₁, hl₁⟩ = pair ⟨l₂, hl₂⟩ := by
      apply Subtype.ext
      exact hpair₁.trans hpair₂.symm
    have hleft : (⟨l₁, hl₁⟩ : {l // l ∈ L}) = ⟨l₂, hl₂⟩ := pair.injective heq
    constructor
    · exact hgp.symm.trans ((congrArg group hleft).trans hgq)
    · exact congrArg Subtype.val hleft
  bans := by
    intro p l r hp x
    obtain ⟨hl, hgroup, hpair⟩ :=
      (mem_matchingEdgeFamily_iff L R pair group p l r).mp hp
    let lsub : {l // l ∈ L} := ⟨l, hl⟩
    change group lsub = p at hgroup
    change (pair lsub).1 = r at hpair
    subst p
    subst r
    rw [leftMatched_matchingEdgeFamily_iff, rightMatched_matchingEdgeFamily_iff]
    exact ban lsub x

end Builder

end SimpleProperBlueprint
