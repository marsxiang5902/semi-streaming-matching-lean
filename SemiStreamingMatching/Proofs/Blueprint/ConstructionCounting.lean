import SemiStreamingMatching.Proofs.Blueprint.Construction
import SemiStreamingMatching.Proofs.Blueprint.RandomWalk
import SemiStreamingMatching.Proofs.Blueprint.StartDistribution
import SemiStreamingMatching.Proofs.Blueprint.MaxClass

open scoped BigOperators

namespace PaperWalkEncoding

section FunctionSplitting

variable {α β ι : Type*} [DecidableEq α]

noncomputable def splitAtEquiv (a : α) :
    (α → β) ≃ β × ({x : α // x ≠ a} → β) where
  toFun f := (f a, fun x => f x.1)
  invFun p := fun x => if h : x = a then p.1 else p.2 ⟨x, h⟩
  left_inv f := by
    funext x
    by_cases h : x = a
    · subst x
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext x
      simp [x.2]

noncomputable def splitEmbeddingEquiv [Fintype ι] (e : ι ↪ α) :
    (α → β) ≃ (ι → β) × ({x : α // x ∉ Set.range e} → β) where
  toFun f := (fun i => f (e i), fun x => f x.1)
  invFun p := fun x =>
    if h : x ∈ Set.range e then p.1 (Classical.choose h) else p.2 ⟨x, h⟩
  left_inv f := by
    funext x
    by_cases h : x ∈ Set.range e
    · simp only [dif_pos h]
      exact congrArg f (Classical.choose_spec h)
    · simp only [dif_neg h]
  right_inv p := by
    apply Prod.ext
    · funext i
      have hmem : e i ∈ Set.range e := ⟨i, rfl⟩
      simp only [dif_pos hmem]
      have hi : Classical.choose hmem = i :=
        e.injective (Classical.choose_spec hmem)
      rw [hi]
    · funext x
      simp only [dif_neg x.2]

end FunctionSplitting

section EncodingEquivalence

variable (S D H : ℕ)

abbrev P := parameterCount D H

def moveCoordEmbedding (d : Fin D) : Fin H ↪ Fin (P D H) where
  toFun k := moveIndex ⟨d.1 + k.1, by omega⟩
  inj' := by
    intro k l h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [moveIndex] at hv
    omega

abbrev StartFree := {i : Fin (P D H) // i ≠ startIndex D H} → Fin S

abbrev DelayFree := {i : Fin (P D H) // i ≠ delayIndex D H} → Fin D

abbrev BitFree (d : Fin D) :=
  {i : Fin (P D H) // i ∉ Set.range (moveCoordEmbedding D H d)} → Bool

abbrev FreeData (d : Fin D) := StartFree S D H × DelayFree D H × BitFree D H d

abbrev RawData :=
  (Fin (P D H) → Fin S) × (Fin (P D H) → Fin D) × (Fin (P D H) → Bool)

noncomputable def vertexRawEquiv :
    Vertex (P D H) (alphabetSize S D) ≃ RawData S D H where
  toFun v :=
    (fun i => (decodeSymbol S D (v i)).1,
      fun i => (decodeSymbol S D (v i)).2.1,
      fun i => (decodeSymbol S D (v i)).2.2)
  invFun r := fun i =>
    (decodeSymbol S D).symm (r.1 i, r.2.1 i, r.2.2 i)
  left_inv v := by
    funext i
    simp
  right_inv r := by
    rcases r with ⟨sf, df, bf⟩
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp

abbrev EncodedData :=
  Σ d : Fin D, Fin S × (Fin H → Bool) × FreeData S D H d

noncomputable def rawEncodedEquiv : RawData S D H ≃ EncodedData S D H where
  toFun r := by
    let ss := splitAtEquiv (β := Fin S) (startIndex D H) r.1
    let ds := splitAtEquiv (β := Fin D) (delayIndex D H) r.2.1
    let bs := splitEmbeddingEquiv (β := Bool) (moveCoordEmbedding D H ds.1) r.2.2
    exact ⟨ds.1, ss.1, bs.1, ss.2, ds.2, bs.2⟩
  invFun e := by
    let sf := (splitAtEquiv (β := Fin S) (startIndex D H)).symm (e.2.1, e.2.2.2.1)
    let df := (splitAtEquiv (β := Fin D) (delayIndex D H)).symm (e.1, e.2.2.2.2.1)
    let bf := (splitEmbeddingEquiv (β := Bool) (moveCoordEmbedding D H e.1)).symm
      (e.2.2.1, e.2.2.2.2.2)
    exact (sf, df, bf)
  left_inv r := by
    rcases r with ⟨sf, df, bf⟩
    simp only
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv e := by
    rcases e with ⟨d, s, w, sfree, dfree, bfree⟩
    simp only
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

noncomputable def vertexEncodedEquiv :
    Vertex (P D H) (alphabetSize S D) ≃ EncodedData S D H :=
  (vertexRawEquiv S D H).trans (rawEncodedEquiv S D H)

@[simp] theorem vertexEncodedEquiv_delay
    (v : Vertex (P D H) (alphabetSize S D)) :
    (vertexEncodedEquiv S D H v).1 = delay v := by
  rfl

@[simp] theorem vertexEncodedEquiv_start
    (v : Vertex (P D H) (alphabetSize S D)) :
    (vertexEncodedEquiv S D H v).2.1 = startToken v := by
  rfl

@[simp] theorem vertexEncodedEquiv_word
    (v : Vertex (P D H) (alphabetSize S D)) (k : Fin H) :
    (vertexEncodedEquiv S D H v).2.2.1 k = moves v k.1 := by
  have hrange : (delay v).1 + k.1 < D + H := by
    have hd := (delay v).2
    have hk := k.2
    omega
  rw [moves, dif_pos hrange]
  rfl

end EncodingEquivalence

section EncodedWalk

variable {N S D H : ℕ}

theorem leftPosition_eq_encodedWord
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (P D H) (alphabetSize S D)) {q : ℕ} (hq : q ≤ H) :
    leftPosition initial v q =
      GamblerWalk.position
        (initial (vertexEncodedEquiv S D H v).2.1)
        (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) q := by
  unfold leftPosition
  rw [vertexEncodedEquiv_start]
  apply GamblerWalk.position_congr_of_lt
  intro r hr
  have hrH : r < H := by omega
  rw [GamblerWalk.movesOfWord_apply _ hrH]
  exact (vertexEncodedEquiv_word S D H v ⟨r, hrH⟩).symm

theorem leftSuccessful_iff_encodedWord
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (P D H) (alphabetSize S D)) :
    leftSuccessful initial v ↔
      GamblerWalk.HitsZeroBy
        (initial (vertexEncodedEquiv S D H v).2.1)
        (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H := by
  unfold leftSuccessful
  rw [GamblerWalk.hitsZeroBy_iff_position_eq_zero,
    GamblerWalk.hitsZeroBy_iff_position_eq_zero]
  change leftPosition initial v H = 0 ↔ _
  rw [leftPosition_eq_encodedWord initial v le_rfl]

theorem walkMax_left_eq_encodedWord
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (P D H) (alphabetSize S D)) :
    walkMax initial false v =
      GamblerWalk.maxPositionUpTo
        (initial (vertexEncodedEquiv S D H v).2.1)
        (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H := by
  apply Nat.le_antisymm
  · obtain ⟨q, hq, hpos⟩ := exists_time_walkMax initial false v
    simp only [Bool.false_eq_true, ↓reduceIte] at hpos
    rw [← hpos, leftPosition_eq_encodedWord initial v (by omega)]
    exact GamblerWalk.position_le_maxPositionUpTo _ _ (by omega)
  · obtain ⟨q, hq, hpos⟩ := GamblerWalk.exists_position_eq_maxPositionUpTo
      (initial (vertexEncodedEquiv S D H v).2.1)
      (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H
    rw [← hpos, ← leftPosition_eq_encodedWord initial v hq]
    unfold walkMax
    apply Finset.le_max'
    simp [visitedValues]
    exact ⟨q, by omega, rfl⟩

theorem maxTime_left_eq_encodedWord
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (P D H) (alphabetSize S D)) :
    maxTime initial false v =
      GamblerWalk.firstMaxTime
        (initial (vertexEncodedEquiv S D H v).2.1)
        (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H := by
  apply Nat.le_antisymm
  · unfold maxTime
    apply Nat.find_min'
    have hfirst := GamblerWalk.firstMaxTime_le
      (initial (vertexEncodedEquiv S D H v).2.1)
      (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H
    refine ⟨by omega, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [leftPosition_eq_encodedWord initial v
      (GamblerWalk.firstMaxTime_le _ _ H), walkMax_left_eq_encodedWord]
    exact GamblerWalk.position_firstMaxTime _ _ H
  · apply GamblerWalk.firstMaxTime_minimal _ _ H (maxTime initial false v)
      (by have := maxTime_lt initial false v; omega)
    rw [← walkMax_left_eq_encodedWord,
      ← leftPosition_eq_encodedWord initial v
        (by have := maxTime_lt initial false v; omega)]
    simpa using position_maxTime initial false v

end EncodedWalk

section WordClasses

variable {N S D H : ℕ}

noncomputable def leftWordClass
    (initial : Fin S → GamblerWalk.State N) (j : ℕ) :
    Finset (Fin S × (Fin H → Bool)) := by
  classical
  exact Finset.univ.filter fun sw ↦
    GamblerWalk.ZeroWithMax (initial sw.1) j sw.2

@[simp] theorem mem_leftWordClass_iff
    (initial : Fin S → GamblerWalk.State N) (j : ℕ)
    (sw : Fin S × (Fin H → Bool)) :
    sw ∈ leftWordClass initial j ↔
      GamblerWalk.ZeroWithMax (initial sw.1) j sw.2 := by
  simp [leftWordClass]

theorem mem_leftClass_iff_encodedWord
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (v : Vertex (P D H) (alphabetSize S D)) :
    v ∈ leftClass initial j t ↔
      GamblerWalk.ZeroWithMax
          (initial (vertexEncodedEquiv S D H v).2.1) j
          (vertexEncodedEquiv S D H v).2.2.1 ∧
        (vertexEncodedEquiv S D H v).1.1 +
          GamblerWalk.firstMaxTime
            (initial (vertexEncodedEquiv S D H v).2.1)
            (GamblerWalk.movesOfWord (vertexEncodedEquiv S D H v).2.2.1) H = t := by
  unfold leftClass
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [leftSuccessful_iff_encodedWord, walkMax_left_eq_encodedWord,
    absoluteMaxTime, maxTime_left_eq_encodedWord]
  have hd : (vertexEncodedEquiv S D H v).1.1 = (delay v).1 :=
    congrArg Fin.val (vertexEncodedEquiv_delay S D H v)
  rw [hd]
  unfold GamblerWalk.ZeroWithMax
  tauto

end WordClasses

section FreeCardinality

variable (S D H : ℕ)

theorem card_StartFree :
    Fintype.card (StartFree S D H) = S ^ (P D H - 1) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_subtype_compl]
  simp

theorem card_DelayFree :
    Fintype.card (DelayFree D H) = D ^ (P D H - 1) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_subtype_compl]
  simp

theorem card_BitFree (d : Fin D) :
    Fintype.card (BitFree D H d) = 2 ^ (D + 2) := by
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_range]
  simp only [Fintype.card_fin]
  unfold P parameterCount
  omega

def freeMultiplicity : ℕ :=
  S ^ (P D H - 1) * D ^ (P D H - 1) * 2 ^ (D + 2)

theorem card_FreeData (d : Fin D) :
    Fintype.card (FreeData S D H d) = freeMultiplicity S D H := by
  simp only [FreeData, Fintype.card_prod, card_StartFree, card_DelayFree, card_BitFree,
    freeMultiplicity]
  ac_rfl

end FreeCardinality

section CentralFibers

variable {N S D H : ℕ}

noncomputable def centralDelay
    (initial : Fin S → GamblerWalk.State N) (t : ℕ)
    (ht : H ≤ t) (htD : t < D) (sw : Fin S × (Fin H → Bool)) : Fin D :=
  ⟨t - GamblerWalk.firstMaxTime (initial sw.1) (GamblerWalk.movesOfWord sw.2) H, by
    have hfirst := GamblerWalk.firstMaxTime_le
      (initial sw.1) (GamblerWalk.movesOfWord sw.2) H
    omega⟩

theorem delay_eq_centralDelay
    (initial : Fin S → GamblerWalk.State N) (t : ℕ)
    (ht : H ≤ t) (htD : t < D) (d : Fin D)
    (sw : Fin S × (Fin H → Bool))
    (habs : d.1 + GamblerWalk.firstMaxTime
      (initial sw.1) (GamblerWalk.movesOfWord sw.2) H = t) :
    d = centralDelay initial t ht htD sw := by
  apply Fin.ext
  simp only [centralDelay]
  have hfirst := GamblerWalk.firstMaxTime_le
    (initial sw.1) (GamblerWalk.movesOfWord sw.2) H
  omega

abbrev CentralFiber
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (ht : H ≤ t) (htD : t < D) :=
  Σ sw : {sw : Fin S × (Fin H → Bool) // sw ∈ leftWordClass initial j},
    FreeData S D H (centralDelay initial t ht htD sw.1)

theorem encoded_repack_eq (e : EncodedData S D H) (d' : Fin D) (h : e.1 = d') :
    (⟨d', e.2.1, e.2.2.1, h ▸ e.2.2.2⟩ : EncodedData S D H) = e := by
  rcases e with ⟨d, s, w, free⟩
  subst d'
  rfl

set_option maxHeartbeats 800000

noncomputable def leftClassCentralFiberEquiv
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (ht : H ≤ t) (htD : t < D) :
    {v // v ∈ leftClass (D := D) (H := H) initial j t} ≃
      CentralFiber initial j t ht htD where
  toFun v := by
    let e := vertexEncodedEquiv S D H v.1
    have hv := (mem_leftClass_iff_encodedWord initial j t v.1).mp v.2
    have hword : (e.2.1, e.2.2.1) ∈ leftWordClass initial j :=
      (mem_leftWordClass_iff initial j _).mpr hv.1
    have hd : e.1 = centralDelay initial t ht htD (e.2.1, e.2.2.1) :=
      delay_eq_centralDelay initial t ht htD e.1 _ hv.2
    exact ⟨⟨(e.2.1, e.2.2.1), hword⟩, hd ▸ e.2.2.2⟩
  invFun z := by
    let e : EncodedData S D H :=
      ⟨centralDelay initial t ht htD z.1.1, z.1.1.1, z.1.1.2, z.2⟩
    let v := (vertexEncodedEquiv S D H).symm e
    refine ⟨v, (mem_leftClass_iff_encodedWord initial j t v).mpr ?_⟩
    have hword := (mem_leftWordClass_iff initial j z.1.1).mp z.1.2
    change GamblerWalk.ZeroWithMax
        (initial (vertexEncodedEquiv S D H v).2.1) j
          (vertexEncodedEquiv S D H v).2.2.1 ∧ _
    rw [show vertexEncodedEquiv S D H v = e by
      exact (vertexEncodedEquiv S D H).apply_symm_apply e]
    refine ⟨hword, ?_⟩
    simp only [e, centralDelay]
    exact Nat.sub_add_cancel
      ((GamblerWalk.firstMaxTime_le
        (initial z.1.1.1) (GamblerWalk.movesOfWord z.1.1.2) H).trans ht)
  left_inv v := by
    apply Subtype.ext
    apply (vertexEncodedEquiv S D H).injective
    let e := vertexEncodedEquiv S D H v.1
    have hv := (mem_leftClass_iff_encodedWord initial j t v.1).mp v.2
    have hd : e.1 = centralDelay initial t ht htD (e.2.1, e.2.2.1) :=
      delay_eq_centralDelay initial t ht htD e.1 _ hv.2
    change vertexEncodedEquiv S D H
      ((vertexEncodedEquiv S D H).symm
        ⟨centralDelay initial t ht htD (e.2.1, e.2.2.1),
          e.2.1, e.2.2.1, hd ▸ e.2.2.2⟩) = e
    rw [(vertexEncodedEquiv S D H).apply_symm_apply]
    exact encoded_repack_eq e _ hd
  right_inv z := by
    rcases z with ⟨⟨sw, hword⟩, free⟩
    let e : EncodedData S D H :=
      ⟨centralDelay initial t ht htD sw, sw.1, sw.2, free⟩
    have he : vertexEncodedEquiv S D H ((vertexEncodedEquiv S D H).symm e) = e :=
      (vertexEncodedEquiv S D H).apply_symm_apply e
    apply Sigma.ext
    · apply Subtype.ext
      change ((vertexEncodedEquiv S D H
        ((vertexEncodedEquiv S D H).symm e)).2.1,
          (vertexEncodedEquiv S D H
            ((vertexEncodedEquiv S D H).symm e)).2.2.1) = sw
      rw [he]
    · change HEq _ free
      dsimp only
      change HEq _ e.2.2.2
      let e0 := vertexEncodedEquiv S D H ((vertexEncodedEquiv S D H).symm e)
      apply HEq.trans (b := e0.2.2.2)
      · exact eqRec_heq _ _
      · exact congr_arg_heq (fun q : EncodedData S D H => q.2.2.2) he

set_option maxHeartbeats 200000

end CentralFibers

section ExactCounts

variable {N S D H : ℕ}

theorem card_CentralFiber
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (ht : H ≤ t) (htD : t < D) :
    Fintype.card (CentralFiber initial j t ht htD) =
      (leftWordClass (H := H) initial j).card * freeMultiplicity S D H := by
  rw [Fintype.card_sigma]
  simp_rw [card_FreeData]
  simp

theorem card_leftClass_eq_wordClass_mul_free
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (ht : H ≤ t) (htD : t < D) :
    (leftClass (D := D) (H := H) initial j t).card =
      (leftWordClass (H := H) initial j).card * freeMultiplicity S D H := by
  calc
    (leftClass (D := D) (H := H) initial j t).card =
        Fintype.card {v // v ∈ leftClass (D := D) (H := H) initial j t} := by simp
    _ = Fintype.card (CentralFiber initial j t ht htD) :=
      Fintype.card_congr (leftClassCentralFiberEquiv initial j t ht htD)
    _ = (leftWordClass (H := H) initial j).card * freeMultiplicity S D H :=
      card_CentralFiber initial j t ht htD

theorem card_EncodedData :
    Fintype.card (EncodedData S D H) =
      D * S * 2 ^ H * freeMultiplicity S D H := by
  rw [Fintype.card_sigma]
  have hterm (d : Fin D) :
      Fintype.card (Fin S × (Fin H → Bool) × FreeData S D H d) =
        S * 2 ^ H * freeMultiplicity S D H := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, card_FreeData]
    ring
  simp_rw [hterm]
  rw [Fin.sum_const]
  simp
  ring

theorem alphabet_pow_eq_essential_mul_free :
    alphabetSize S D ^ P D H =
      D * S * 2 ^ H * freeMultiplicity S D H := by
  calc
    alphabetSize S D ^ P D H =
        Fintype.card (Vertex (P D H) (alphabetSize S D)) := by
          simp [Vertex]
    _ = Fintype.card (EncodedData S D H) :=
      Fintype.card_congr (vertexEncodedEquiv S D H)
    _ = D * S * 2 ^ H * freeMultiplicity S D H := card_EncodedData

theorem leftClass_density_eq_wordClass_density_div
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (hS : 0 < S) (ht : H ≤ t) (htD : t < D) :
    ((leftClass (D := D) (H := H) initial j t).card : ℝ) /
        (alphabetSize S D : ℝ) ^ P D H =
      (((leftWordClass (H := H) initial j).card : ℝ) / ((S : ℝ) * (2 : ℝ) ^ H)) /
        (D : ℝ) := by
  rw [card_leftClass_eq_wordClass_mul_free initial j t ht htD]
  rw [show (alphabetSize S D : ℝ) ^ P D H =
      ((D * S * 2 ^ H * freeMultiplicity S D H : ℕ) : ℝ) by
    exact_mod_cast alphabet_pow_eq_essential_mul_free (S := S) (D := D) (H := H)]
  push_cast
  have hD : 0 < D := by omega
  have hfreeNat : 0 < freeMultiplicity S D H := by
    unfold freeMultiplicity
    positivity
  have hSr : (S : ℝ) ≠ 0 := by positivity
  have hDr : (D : ℝ) ≠ 0 := by positivity
  have hfr : (freeMultiplicity S D H : ℝ) ≠ 0 := by positivity
  field_simp [hSr, hDr, hfr]
  ring

theorem rightClass_density_eq_wordClass_density_div
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (hS : 0 < S) (ht : H ≤ t) (htD : t < D) :
    ((rightClass (D := D) (H := H) initial j t).card : ℝ) /
        (alphabetSize S D : ℝ) ^ P D H =
      (((leftWordClass (H := H) initial j).card : ℝ) / ((S : ℝ) * (2 : ℝ) ^ H)) /
        (D : ℝ) := by
  rw [← card_leftClass_eq_card_rightClass (D := D) (H := H) initial j t]
  exact leftClass_density_eq_wordClass_density_div initial j t hS ht htD

end ExactCounts

section AveragedWordCount

variable {N S H : ℕ}

noncomputable def leftWordClassEquivAmbientSigma
    (initial : Fin S → GamblerWalk.State N) (j : ℕ) :
    {sw // sw ∈ leftWordClass (H := H) initial j} ≃
      Σ s : Fin S, {w : Fin H → Bool //
        w ∈ GamblerWalk.ambientMaxZeroWords N H (initial s) j} where
  toFun sw := ⟨sw.1.1, sw.1.2, by
    simpa [GamblerWalk.ambientMaxZeroWords] using
      (mem_leftWordClass_iff initial j sw.1).mp sw.2⟩
  invFun z := ⟨(z.1, z.2.1), by
    apply (mem_leftWordClass_iff initial j _).mpr
    simpa [GamblerWalk.ambientMaxZeroWords] using
      (Finset.mem_filter.mp z.2.2).2⟩
  left_inv sw := by rfl
  right_inv z := by rfl

theorem card_leftWordClass_eq_sum_ambient
    (initial : Fin S → GamblerWalk.State N) (j : ℕ) :
    (leftWordClass (H := H) initial j).card =
      ∑ s : Fin S, (GamblerWalk.ambientMaxZeroWords N H (initial s) j).card := by
  classical
  calc
    (leftWordClass (H := H) initial j).card =
        Fintype.card {sw // sw ∈ leftWordClass (H := H) initial j} :=
      (Fintype.card_coe (leftWordClass (H := H) initial j)).symm
    _ = Fintype.card (Σ s : Fin S, {w : Fin H → Bool //
          w ∈ GamblerWalk.ambientMaxZeroWords N H (initial s) j}) :=
      Fintype.card_congr (leftWordClassEquivAmbientSigma initial j)
    _ = ∑ s : Fin S,
        (GamblerWalk.ambientMaxZeroWords N H (initial s) j).card := by
      rw [Fintype.card_sigma]
      simp

theorem leftWordClass_density_eq_average_ambient
    (initial : Fin S → GamblerWalk.State N) (j : ℕ) :
    ((leftWordClass (H := H) initial j).card : ℝ) /
        ((S : ℝ) * (2 : ℝ) ^ H) =
      (∑ s : Fin S,
        GamblerWalk.ambientMaxZeroProbability (H := H) (initial s) j) / (S : ℝ) := by
  rw [card_leftWordClass_eq_sum_ambient]
  unfold GamblerWalk.ambientMaxZeroProbability
  rw [← Finset.sum_div]
  push_cast
  ring

end AveragedWordCount

section StartDistributionEstimate

theorem startWordClass_density_approx_maxMass
    {m K k j : ℕ} (hNK : 2 * m ≤ K) (hj : 0 < j) (hjN : j < 2 * m) :
    |((leftWordClass (H := k * K) (StartDistribution.start m) j).card : ℝ) /
        ((StartDistribution.sampleCount m : ℝ) * (2 : ℝ) ^ (k * K)) -
      StartDistribution.maxMass m j| ≤ GamblerWalk.failureRatio K ^ k := by
  letI : Nonempty (Fin (StartDistribution.sampleCount m)) :=
    ⟨⟨0, StartDistribution.sampleCount_pos m⟩⟩
  rw [leftWordClass_density_eq_average_ambient]
  unfold StartDistribution.maxMass
  simpa using GamblerWalk.average_ambientMaxZeroProbability_approx
    (S := Fin (StartDistribution.sampleCount m)) hNK hj hjN
      (StartDistribution.start m)

theorem start_leftClass_density_approx_maxMass_div
    {m K k D j t : ℕ} (hNK : 2 * m ≤ K) (hj : 0 < j) (hjN : j < 2 * m)
    (ht : k * K ≤ t) (htD : t < D) :
    |((leftClass (D := D) (H := k * K) (StartDistribution.start m) j t).card : ℝ) /
          (alphabetSize (StartDistribution.sampleCount m) D : ℝ) ^ P D (k * K) -
        StartDistribution.maxMass m j / (D : ℝ)| ≤
      GamblerWalk.failureRatio K ^ k / (D : ℝ) := by
  rw [leftClass_density_eq_wordClass_density_div
    (StartDistribution.start m) j t (StartDistribution.sampleCount_pos m) ht htD]
  have happ := startWordClass_density_approx_maxMass (k := k) hNK hj hjN
  have hD : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  rw [← sub_div, abs_div, abs_of_pos hD]
  apply (div_le_div_iff hD hD).2
  exact mul_le_mul_of_nonneg_right happ hD.le

theorem start_rightClass_density_approx_maxMass_div
    {m K k D j t : ℕ} (hNK : 2 * m ≤ K) (hj : 0 < j) (hjN : j < 2 * m)
    (ht : k * K ≤ t) (htD : t < D) :
    |((rightClass (D := D) (H := k * K) (StartDistribution.start m) j t).card : ℝ) /
          (alphabetSize (StartDistribution.sampleCount m) D : ℝ) ^ P D (k * K) -
        StartDistribution.maxMass m j / (D : ℝ)| ≤
      GamblerWalk.failureRatio K ^ k / (D : ℝ) := by
  rw [← card_leftClass_eq_card_rightClass (D := D) (H := k * K)
    (StartDistribution.start m) j t]
  exact start_leftClass_density_approx_maxMass_div hNK hj hjN ht htD

theorem start_rightClass_density_approx_reflectedMaxMass_div
    {m K k D j t : ℕ} (hm : 0 < m) (hNK : 2 * m ≤ K)
    (hj : 1 ≤ j) (hjN : j < 2 * m) (ht : k * K ≤ t) (htD : t < D) :
    |((rightClass (D := D) (H := k * K) (StartDistribution.start m) j t).card : ℝ) /
          (alphabetSize (StartDistribution.sampleCount m) D : ℝ) ^ P D (k * K) -
        StartDistribution.maxMass m (2 * m - j) / (D : ℝ)| ≤
      GamblerWalk.failureRatio K ^ k / (D : ℝ) := by
  rw [← StartDistribution.maxMass_symm hm hj hjN]
  exact start_rightClass_density_approx_maxMass_div hNK (by omega) hjN ht htD

end StartDistributionEstimate

end PaperWalkEncoding
