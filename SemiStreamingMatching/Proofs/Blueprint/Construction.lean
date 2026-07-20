import SemiStreamingMatching.Proofs.Blueprint.Blueprint
import SemiStreamingMatching.Proofs.Blueprint.RandomWalk
import SemiStreamingMatching.Proofs.Blueprint.FiniteMatching
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators

structure IndexedBlueprintData (P C : ℕ) where
  edgeMultiplicity : Fin P → ℕ
  left : (p : Fin P) → Fin (edgeMultiplicity p) → Vertex P C
  right : (p : Fin P) → Fin (edgeMultiplicity p) → Vertex P C
  left_injective :
    ∀ {p q : Fin P} {i : Fin (edgeMultiplicity p)} {j : Fin (edgeMultiplicity q)},
      left p i = left q j → p = q ∧ HEq i j
  right_injective :
    ∀ {p q : Fin P} {i : Fin (edgeMultiplicity p)} {j : Fin (edgeMultiplicity q)},
      right p i = right q j → p = q ∧ HEq i j
  ban :
    ∀ (p : Fin P) (i : Fin (edgeMultiplicity p)) (x : Suffix P C p),
      (¬ ∃ (q : Fin P) (j : Fin (edgeMultiplicity q)),
          left q j = patchVertex p (left p i) x) ∨
      (¬ ∃ (q : Fin P) (j : Fin (edgeMultiplicity q)),
          right q j = patchVertex p (right p i) x)

namespace IndexedBlueprintData

variable {P C : ℕ}

noncomputable def edgeFamily (D : IndexedBlueprintData P C) : EdgeFamily P C := by
  classical
  exact fun p => Finset.univ.image fun i : Fin (D.edgeMultiplicity p) => (D.left p i, D.right p i)

@[simp] theorem mem_edgeFamily_iff (D : IndexedBlueprintData P C) (p : Fin P)
    (l r : Vertex P C) :
    (l, r) ∈ D.edgeFamily p ↔
      ∃ i : Fin (D.edgeMultiplicity p), D.left p i = l ∧ D.right p i = r := by
  classical
  simp [edgeFamily, and_comm]

@[simp] theorem leftMatched_edgeFamily_iff (D : IndexedBlueprintData P C)
    (l : Vertex P C) :
    leftMatched D.edgeFamily l ↔
      ∃ (p : Fin P) (i : Fin (D.edgeMultiplicity p)), D.left p i = l := by
  constructor
  · rintro ⟨p, r, hr⟩
    rw [D.mem_edgeFamily_iff] at hr
    obtain ⟨i, hi, -⟩ := hr
    exact ⟨p, i, hi⟩
  · rintro ⟨p, i, rfl⟩
    exact ⟨p, D.right p i, D.mem_edgeFamily_iff p _ _ |>.2 ⟨i, rfl, rfl⟩⟩

@[simp] theorem rightMatched_edgeFamily_iff (D : IndexedBlueprintData P C)
    (r : Vertex P C) :
    rightMatched D.edgeFamily r ↔
      ∃ (p : Fin P) (i : Fin (D.edgeMultiplicity p)), D.right p i = r := by
  constructor
  · rintro ⟨p, l, hl⟩
    rw [D.mem_edgeFamily_iff] at hl
    obtain ⟨i, -, hi⟩ := hl
    exact ⟨p, i, hi⟩
  · rintro ⟨p, i, rfl⟩
    exact ⟨p, D.left p i, D.mem_edgeFamily_iff p _ _ |>.2 ⟨i, rfl, rfl⟩⟩

noncomputable def toBlueprint (D : IndexedBlueprintData P C)
    (hP : 0 < P) (hC : 0 < C) : SimpleProperBlueprint where
  P := P
  hP := hP
  C := C
  hC := hC
  E := D.edgeFamily
  left_matching := by
    intro p q l r₁ r₂ hp hq
    rw [D.mem_edgeFamily_iff] at hp hq
    obtain ⟨i, hil, hir⟩ := hp
    obtain ⟨j, hjl, hjr⟩ := hq
    obtain ⟨hpq, hij⟩ := D.left_injective (hil.trans hjl.symm)
    subst q
    have hij' : i = j := eq_of_heq hij
    subst j
    exact ⟨rfl, hir.symm.trans hjr⟩
  right_matching := by
    intro p q l₁ l₂ r hp hq
    rw [D.mem_edgeFamily_iff] at hp hq
    obtain ⟨i, hil, hir⟩ := hp
    obtain ⟨j, hjl, hjr⟩ := hq
    obtain ⟨hpq, hij⟩ := D.right_injective (hir.trans hjr.symm)
    subst q
    have hij' : i = j := eq_of_heq hij
    subst j
    exact ⟨rfl, hil.symm.trans hjl⟩
  bans := by
    intro p l r hp x
    rw [D.mem_edgeFamily_iff] at hp
    obtain ⟨i, rfl, rfl⟩ := hp
    simpa [D.leftMatched_edgeFamily_iff, D.rightMatched_edgeFamily_iff] using D.ban p i x

noncomputable def edgeEmbedding (D : IndexedBlueprintData P C) (hP : 0 < P) (hC : 0 < C) :
    (Sigma fun p : Fin P => Fin (D.edgeMultiplicity p)) →
      { e : (D.toBlueprint hP hC).EdgeOver //
        e.2 ∈ (D.toBlueprint hP hC).E e.1 } := by
  classical
  intro e
  exact ⟨⟨e.1, (D.left e.1 e.2, D.right e.1 e.2)⟩,
    D.mem_edgeFamily_iff e.1 _ _ |>.2 ⟨e.2, rfl, rfl⟩⟩

theorem edgeEmbedding_injective (D : IndexedBlueprintData P C) (hP : 0 < P) (hC : 0 < C) :
    Function.Injective (D.edgeEmbedding hP hC) := by
  intro a b hab
  rcases a with ⟨p, i⟩
  rcases b with ⟨q, j⟩
  have hpq : p = q := congrArg (fun e => e.1.1) hab
  subst q
  have hl : D.left p i = D.left p j := congrArg (fun e => e.1.2.1) hab
  have hij : i = j := eq_of_heq (D.left_injective hl).2
  subst j
  rfl

theorem sum_edgeMultiplicity_le_edgeCount (D : IndexedBlueprintData P C)
    (hP : 0 < P) (hC : 0 < C) :
    ∑ p, D.edgeMultiplicity p ≤ (D.toBlueprint hP hC).edgeCount := by
  classical
  unfold SimpleProperBlueprint.edgeCount
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_le_of_injective (D.edgeEmbedding hP hC)
      (D.edgeEmbedding_injective hP hC)

@[simp] theorem vertexCount_toBlueprint (D : IndexedBlueprintData P C)
    (hP : 0 < P) (hC : 0 < C) :
    (D.toBlueprint hP hC).vertexCount = C ^ P := by
  change Fintype.card (Fin P → Fin C) = C ^ P
  simp

theorem indexedDensity_le_value (D : IndexedBlueprintData P C)
    (hP : 0 < P) (hC : 0 < C) :
    ((∑ p, D.edgeMultiplicity p : ℕ) : ℝ) / (C ^ P : ℕ) ≤
      (D.toBlueprint hP hC).value := by
  rw [SimpleProperBlueprint.value, D.vertexCount_toBlueprint]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast D.sum_edgeMultiplicity_le_edgeCount hP hC)
    (by positivity)

end IndexedBlueprintData

noncomputable def paperLowerBound (m : ℕ) : ℝ :=
  (1 - 1 / (m : ℝ)) *
      ((2 / 3 : ℝ) * ((m : ℝ) / ((m : ℝ) + 1 / 3))) -
    3 * (m : ℝ) * (1 / 2 : ℝ) ^ m

theorem paperLowerBound_eq (m : ℕ) (hm : 0 < m) :
    paperLowerBound m =
      (1 - 1 / (m : ℝ)) * (2 * (m : ℝ) / (3 * (m : ℝ) + 1)) -
        3 * (m : ℝ) * (1 / 2 : ℝ) ^ m := by
  unfold paperLowerBound
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

theorem tendsto_paperLowerBound :
    Filter.Tendsto paperLowerBound Filter.atTop (nhds ((2 : ℝ) / 3)) := by
  have h₁ : Filter.Tendsto (fun m : ℕ ↦ (1 : ℝ) - 1 / (m : ℝ))
      Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat using 1 <;> norm_num
  have h₂ : Filter.Tendsto
      (fun m : ℕ ↦ (2 / 3 : ℝ) * ((m : ℝ) / ((m : ℝ) + 1 / 3)))
      Filter.atTop (nhds ((2 : ℝ) / 3)) := by
    convert tendsto_const_nhds.mul (tendsto_natCast_div_add_atTop (1 / 3 : ℝ)) using 1 <;>
      norm_num
  have h₃ : Filter.Tendsto
      (fun m : ℕ ↦ 3 * (m : ℝ) * (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_self_mul_const_pow_of_lt_one (r := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)).const_mul (3 : ℝ)
  simpa only [paperLowerBound, one_mul, sub_zero] using (h₁.mul h₂).sub h₃

theorem exists_paperLowerBound_near_two_thirds (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (2 : ℝ) / 3 - ε < paperLowerBound m := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 tendsto_paperLowerBound) ε hε
  let m := max N 1
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  have hmclose := hN m (le_max_left N 1)
  refine ⟨m, hm, ?_⟩
  rw [Real.dist_eq] at hmclose
  have hlower := (abs_lt.mp hmclose).1
  linarith

namespace PaperWalkEncoding

abbrev Symbol (S D : ℕ) := Fin S × Fin D × Bool

abbrev alphabetSize (S D : ℕ) := Fintype.card (Symbol S D)

abbrev parameterCount (D H : ℕ) := D + H + 2

noncomputable def decodeSymbol (S D : ℕ) :
    Fin (alphabetSize S D) ≃ Symbol S D :=
  (Fintype.equivFin (Symbol S D)).symm

def flipSymbol {S D : ℕ} (a : Symbol S D) : Symbol S D :=
  (a.1, a.2.1, !a.2.2)

@[simp] theorem flipSymbol_flipSymbol {S D : ℕ} (a : Symbol S D) :
    flipSymbol (flipSymbol a) = a := by
  rcases a with ⟨s, d, b⟩
  cases b <;> rfl

noncomputable def flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    Vertex (parameterCount D H) (alphabetSize S D) :=
  fun i ↦ (decodeSymbol S D).symm (flipSymbol (decodeSymbol S D (v i)))

@[simp] theorem flipVertex_flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    flipVertex (flipVertex v) = v := by
  funext i
  simp [flipVertex]

noncomputable def flipVertexEquiv (S D H : ℕ) :
    Vertex (parameterCount D H) (alphabetSize S D) ≃
      Vertex (parameterCount D H) (alphabetSize S D) where
  toFun := flipVertex
  invFun := flipVertex
  left_inv := flipVertex_flipVertex
  right_inv := flipVertex_flipVertex

@[simp] theorem alphabetSize_eq (S D : ℕ) : alphabetSize S D = S * D * 2 := by
  simp [alphabetSize, Symbol, Nat.mul_assoc]

def startIndex (D H : ℕ) : Fin (parameterCount D H) := ⟨0, by
  simp [parameterCount]⟩

def delayIndex (D H : ℕ) : Fin (parameterCount D H) := ⟨1, by
  simp [parameterCount]⟩

noncomputable def startToken {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : Fin S :=
  (decodeSymbol S D (v (startIndex D H))).1

noncomputable def delay {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : Fin D :=
  (decodeSymbol S D (v (delayIndex D H))).2.1

@[simp] theorem startToken_flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    startToken (flipVertex v) = startToken v := by
  simp [startToken, flipVertex, flipSymbol]

@[simp] theorem delay_flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    delay (flipVertex v) = delay v := by
  simp [delay, flipVertex, flipSymbol]

def moveIndex {D H : ℕ} (t : Fin (D + H)) : Fin (parameterCount D H) :=
  ⟨t.1 + 2, by
    have ht := t.2
    simp only [parameterCount]
    omega⟩

noncomputable def moves {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : ℕ → Bool :=
  fun t ↦
    if ht : (delay v).1 + t < D + H then
      (decodeSymbol S D (v (moveIndex ⟨(delay v).1 + t, ht⟩))).2.2
    else
      false

noncomputable def reflectedMoves {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : ℕ → Bool :=
  fun t ↦
    if ht : (delay v).1 + t < D + H then
      !((decodeSymbol S D (v (moveIndex ⟨(delay v).1 + t, ht⟩))).2.2)
    else
      false

@[simp] theorem moves_flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (t : ℕ) :
    moves (flipVertex v) t = reflectedMoves v t := by
  by_cases ht : (delay v).1 + t < D + H
  · simp only [reflectedMoves, dif_pos ht, moves, delay_flipVertex]
    simp [flipVertex, flipSymbol]
  · simp [moves, reflectedMoves, ht]

@[simp] theorem reflectedMoves_flipVertex {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    reflectedMoves (flipVertex v) = moves v := by
  funext t
  rw [← moves_flipVertex (flipVertex v) t, flipVertex_flipVertex]

noncomputable def leftPosition {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (t : ℕ) :
    GamblerWalk.State N :=
  GamblerWalk.position (initial (startToken v)) (moves v) t

noncomputable def rightPosition {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (t : ℕ) :
    GamblerWalk.State N :=
  GamblerWalk.position (initial (startToken v)) (reflectedMoves v) t

noncomputable def bitAt {S D H : ℕ}
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : Fin (D + H)) : Bool :=
  (decodeSymbol S D (v (moveIndex a))).2.2

noncomputable def leftAbsolutePosition {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ) :
    GamblerWalk.State N :=
  if h : (delay v).1 ≤ a then leftPosition initial v (a - (delay v).1)
  else initial (startToken v)

noncomputable def rightAbsolutePosition {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ) :
    GamblerWalk.State N :=
  if h : (delay v).1 ≤ a then rightPosition initial v (a - (delay v).1)
  else initial (startToken v)

theorem leftAbsolutePosition_succ {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ)
    (hda : (delay v).1 ≤ a) (ha : a < D + H) :
    leftAbsolutePosition initial v (a + 1) =
      GamblerWalk.step (leftAbsolutePosition initial v a) (bitAt v ⟨a, ha⟩) := by
  rw [leftAbsolutePosition, dif_pos (hda.trans (Nat.le_succ a)),
    leftAbsolutePosition, dif_pos hda, leftPosition, leftPosition]
  have hsub : a + 1 - (delay v).1 = (a - (delay v).1) + 1 := by omega
  rw [hsub, GamblerWalk.position_succ]
  congr 1
  have hadd : (delay v).1 + (a - (delay v).1) = a := by omega
  simp [moves, bitAt, hadd, ha]

theorem rightAbsolutePosition_succ {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ)
    (hda : (delay v).1 ≤ a) (ha : a < D + H) :
    rightAbsolutePosition initial v (a + 1) =
      GamblerWalk.step (rightAbsolutePosition initial v a) (!(bitAt v ⟨a, ha⟩)) := by
  rw [rightAbsolutePosition, dif_pos (hda.trans (Nat.le_succ a)),
    rightAbsolutePosition, dif_pos hda, rightPosition, rightPosition]
  have hsub : a + 1 - (delay v).1 = (a - (delay v).1) + 1 := by omega
  rw [hsub, GamblerWalk.position_succ]
  congr 1
  have hadd : (delay v).1 + (a - (delay v).1) = a := by omega
  simp [reflectedMoves, bitAt, hadd, ha]

theorem absolute_positions_reflect_of_common_bits {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (l r : Vertex (parameterCount D H) (alphabetSize S D))
    (t u : ℕ)
    (hdl : (delay l).1 ≤ t) (hdr : (delay r).1 ≤ t)
    (hbound : t + u ≤ D + H)
    (hstart :
      rightAbsolutePosition initial r t =
        GamblerWalk.reflect (leftAbsolutePosition initial l t))
    (hbits : ∀ a (hta : t ≤ a) (ha : a < D + H),
      bitAt r ⟨a, ha⟩ = bitAt l ⟨a, ha⟩) :
    rightAbsolutePosition initial r (t + u) =
      GamblerWalk.reflect (leftAbsolutePosition initial l (t + u)) := by
  induction u with
  | zero => simpa using hstart
  | succ u ih =>
      have ha : t + u < D + H := by omega
      have hdla : (delay l).1 ≤ t + u := hdl.trans (by omega)
      have hdra : (delay r).1 ≤ t + u := hdr.trans (by omega)
      rw [Nat.add_succ, rightAbsolutePosition_succ initial r (t + u) hdra ha,
        leftAbsolutePosition_succ initial l (t + u) hdla ha, ih (by omega)]
      rw [hbits (t + u) (by omega) ha]
      exact GamblerWalk.step_reflect _ _

theorem startToken_patchVertex {S D H : ℕ} {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1) :
    startToken (patchVertex p v x) = startToken v := by
  have hnot : ¬p ≤ startIndex D H := by
    intro h
    have hv : p.1 ≤ (startIndex D H).1 := Fin.le_iff_val_le_val.mp h
    simp [startIndex] at hv
    omega
  simp [startToken, patchVertex, hnot]

theorem delay_patchVertex {S D H : ℕ} {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1) :
    delay (patchVertex p v x) = delay v := by
  have hnot : ¬p ≤ delayIndex D H := by
    intro h
    have hv : p.1 ≤ (delayIndex D H).1 := Fin.le_iff_val_le_val.mp h
    simp [delayIndex] at hv
    omega
  simp [delay, patchVertex, hnot]

theorem bitAt_patchVertex_eq {S D H : ℕ} {p : Fin (parameterCount D H)}
    (l r : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (a : Fin (D + H)) (hpa : p.1 ≤ a.1 + 2) :
    bitAt (patchVertex p l x) a = bitAt (patchVertex p r x) a := by
  have hpidx : p ≤ moveIndex a := by
    apply Fin.le_iff_val_le_val.mpr
    exact hpa
  simp [bitAt, patchVertex, hpidx]

theorem bitAt_patchVertex_of_lt {S D H : ℕ} {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (a : Fin (D + H)) (hap : a.1 + 2 < p.1) :
    bitAt (patchVertex p v x) a = bitAt v a := by
  have hnot : ¬p ≤ moveIndex a := by
    intro h
    have hv : p.1 ≤ (moveIndex a).1 := Fin.le_iff_val_le_val.mp h
    simp [moveIndex] at hv
    omega
  simp [bitAt, patchVertex, hnot]

theorem moves_patchVertex_of_before {S D H : ℕ} {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1) (s : ℕ)
    (hs : (delay v).1 + s + 2 < p.1) :
    moves (patchVertex p v x) s = moves v s := by
  rw [moves, delay_patchVertex v x hp, moves]
  by_cases hrange : (delay v).1 + s < D + H
  · simp only [dif_pos hrange]
    exact bitAt_patchVertex_of_lt v x ⟨(delay v).1 + s, hrange⟩ hs
  · simp [hrange]

theorem reflectedMoves_patchVertex_of_before {S D H : ℕ}
    {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1) (s : ℕ)
    (hs : (delay v).1 + s + 2 < p.1) :
    reflectedMoves (patchVertex p v x) s = reflectedMoves v s := by
  rw [reflectedMoves, delay_patchVertex v x hp, reflectedMoves]
  by_cases hrange : (delay v).1 + s < D + H
  · simp only [dif_pos hrange]
    simpa [bitAt] using congrArg (fun b : Bool ↦ !b)
      (bitAt_patchVertex_of_lt v x ⟨(delay v).1 + s, hrange⟩ hs)
  · simp only [dif_neg hrange]

theorem GamblerWalk.position_congr_until {N : ℕ}
    {start₁ start₂ : GamblerWalk.State N} {moves₁ moves₂ : ℕ → Bool}
    (t : ℕ) (hstart : start₁ = start₂)
    (hmoves : ∀ s < t, moves₁ s = moves₂ s) :
    GamblerWalk.position start₁ moves₁ t = GamblerWalk.position start₂ moves₂ t := by
  subst start₂
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GamblerWalk.position_succ, GamblerWalk.position_succ,
        ih (fun s hs ↦ hmoves s (by omega))]
      exact congrArg _ (hmoves t (by omega))

@[simp] theorem rightPosition_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (t : ℕ) :
    rightPosition initial (flipVertex v) t = leftPosition initial v t := by
  simp [rightPosition, leftPosition]

@[simp] theorem leftPosition_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (t : ℕ) :
    leftPosition initial (flipVertex v) t = rightPosition initial v t := by
  simp only [leftPosition, rightPosition, startToken_flipVertex]
  have hm : moves (flipVertex v) = reflectedMoves v := by
    funext s
    exact moves_flipVertex v s
  rw [hm]

noncomputable def leftSuccessful {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : Prop :=
  GamblerWalk.HitsZeroBy (initial (startToken v)) (moves v) H

noncomputable def rightSuccessful {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : Prop :=
  GamblerWalk.HitsZeroBy (initial (startToken v)) (reflectedMoves v) H

@[simp] theorem rightSuccessful_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    rightSuccessful initial (flipVertex v) ↔ leftSuccessful initial v := by
  simp [rightSuccessful, leftSuccessful]

@[simp] theorem leftSuccessful_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    leftSuccessful initial (flipVertex v) ↔ rightSuccessful initial v := by
  simp only [rightSuccessful, leftSuccessful, startToken_flipVertex]
  have hm : moves (flipVertex v) = reflectedMoves v := by
    funext s
    exact moves_flipVertex v s
  rw [hm]

theorem leftSuccessful_position_H {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (h : leftSuccessful initial v) :
    leftPosition initial v H = 0 := by
  exact (GamblerWalk.hitsZeroBy_iff_position_eq_zero _ _ _).mp h

theorem rightSuccessful_position_H {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (h : rightSuccessful initial v) :
    rightPosition initial v H = 0 := by
  exact (GamblerWalk.hitsZeroBy_iff_position_eq_zero _ _ _).mp h

@[simp] theorem leftAbsolutePosition_horizon {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    leftAbsolutePosition initial v ((delay v).1 + H) =
      leftPosition initial v H := by
  simp [leftAbsolutePosition]

@[simp] theorem rightAbsolutePosition_horizon {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    rightAbsolutePosition initial v ((delay v).1 + H) =
      rightPosition initial v H := by
  simp [rightAbsolutePosition]

theorem leftPosition_H_eq_top_of_absolute_eq_top {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ)
    (hda : (delay v).1 ≤ a) (ha : a ≤ (delay v).1 + H)
    (habs : leftAbsolutePosition initial v a =
      (⟨N, by omega⟩ : GamblerWalk.State N)) :
    leftPosition initial v H = ⟨N, by omega⟩ := by
  rw [leftAbsolutePosition, dif_pos hda] at habs
  let s := H - (a - (delay v).1)
  have hadd : a - (delay v).1 + s = H := by
    dsimp [s]
    omega
  have hboundary : GamblerWalk.AtBoundary
      (GamblerWalk.position (initial (startToken v)) (moves v)
        (a - (delay v).1)) := by
    change GamblerWalk.AtBoundary (leftPosition initial v (a - (delay v).1))
    rw [habs]
    simp
  have hstay := GamblerWalk.position_add_eq_of_atBoundary
    (initial (startToken v)) (moves v) (a - (delay v).1) s
    hboundary
  change leftPosition initial v (a - (delay v).1 + s) =
    leftPosition initial v (a - (delay v).1) at hstay
  rw [hadd] at hstay
  exact hstay.trans habs

theorem rightPosition_H_eq_top_of_absolute_eq_top {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) (a : ℕ)
    (hda : (delay v).1 ≤ a) (ha : a ≤ (delay v).1 + H)
    (habs : rightAbsolutePosition initial v a =
      (⟨N, by omega⟩ : GamblerWalk.State N)) :
    rightPosition initial v H = ⟨N, by omega⟩ := by
  rw [rightAbsolutePosition, dif_pos hda] at habs
  let s := H - (a - (delay v).1)
  have hadd : a - (delay v).1 + s = H := by
    dsimp [s]
    omega
  have hboundary : GamblerWalk.AtBoundary
      (GamblerWalk.position (initial (startToken v)) (reflectedMoves v)
        (a - (delay v).1)) := by
    change GamblerWalk.AtBoundary (rightPosition initial v (a - (delay v).1))
    rw [habs]
    simp
  have hstay := GamblerWalk.position_add_eq_of_atBoundary
    (initial (startToken v)) (reflectedMoves v) (a - (delay v).1) s
    hboundary
  change rightPosition initial v (a - (delay v).1 + s) =
    rightPosition initial v (a - (delay v).1) at hstay
  rw [hadd] at hstay
  exact hstay.trans habs

noncomputable instance leftSuccessful_decidable {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    Decidable (leftSuccessful initial v) := by
  unfold leftSuccessful
  infer_instance

noncomputable instance rightSuccessful_decidable {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    Decidable (rightSuccessful initial v) := by
  unfold rightSuccessful
  infer_instance

noncomputable def visitedValues {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : Finset ℕ := by
  classical
  exact (Finset.range (H + 1)).image fun t ↦
    if right then (rightPosition initial v t).1 else (leftPosition initial v t).1

theorem visitedValues_nonempty {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    (visitedValues initial right v).Nonempty := by
  classical
  refine ⟨(if right then (rightPosition initial v 0).1 else (leftPosition initial v 0).1), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨0, by simp, rfl⟩

noncomputable def walkMax {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : ℕ :=
  (visitedValues initial right v).max' (visitedValues_nonempty initial right v)

theorem exists_time_walkMax {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    ∃ t < H + 1,
      (if right then (rightPosition initial v t).1 else (leftPosition initial v t).1) =
        walkMax initial right v := by
  classical
  have hmem : walkMax initial right v ∈ visitedValues initial right v :=
    Finset.max'_mem _ _
  simpa [visitedValues] using hmem

noncomputable def maxTime {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : ℕ :=
  Nat.find (exists_time_walkMax initial right v)

theorem maxTime_lt {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    maxTime initial right v < H + 1 :=
  (Nat.find_spec (exists_time_walkMax initial right v)).1

theorem position_maxTime {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    (if right then (rightPosition initial v (maxTime initial right v)).1
      else (leftPosition initial v (maxTime initial right v)).1) =
        walkMax initial right v :=
  (Nat.find_spec (exists_time_walkMax initial right v)).2

noncomputable def absoluteMaxTime {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (right : Bool)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) : ℕ :=
  (delay v).1 + maxTime initial right v

theorem leftPosition_patchVertex_at_maxTime {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroup : (delay v).1 + maxTime initial false v + 2 = p.1) :
    leftPosition initial (patchVertex p v x) (maxTime initial false v) =
      leftPosition initial v (maxTime initial false v) := by
  apply GamblerWalk.position_congr_until
  · rw [startToken_patchVertex v x hp]
  · intro s hs
    exact moves_patchVertex_of_before v x hp s (by omega)

theorem rightPosition_patchVertex_at_maxTime {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroup : (delay v).1 + maxTime initial true v + 2 = p.1) :
    rightPosition initial (patchVertex p v x) (maxTime initial true v) =
      rightPosition initial v (maxTime initial true v) := by
  apply GamblerWalk.position_congr_until
  · rw [startToken_patchVertex v x hp]
  · intro s hs
    exact reflectedMoves_patchVertex_of_before v x hp s (by omega)

theorem leftAbsolutePosition_patchVertex_at_group {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroup : (delay v).1 + maxTime initial false v + 2 = p.1) :
    leftAbsolutePosition initial (patchVertex p v x) (p.1 - 2) =
      leftPosition initial v (maxTime initial false v) := by
  have hd := delay_patchVertex v x hp
  have hle : (delay (patchVertex p v x)).1 ≤ p.1 - 2 := by
    rw [hd]
    omega
  rw [leftAbsolutePosition, dif_pos hle]
  have hsub : p.1 - 2 - (delay (patchVertex p v x)).1 =
      maxTime initial false v := by
    rw [hd]
    omega
  rw [hsub]
  exact leftPosition_patchVertex_at_maxTime initial v x hp hgroup

theorem rightAbsolutePosition_patchVertex_at_group {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p : Fin (parameterCount D H)}
    (v : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroup : (delay v).1 + maxTime initial true v + 2 = p.1) :
    rightAbsolutePosition initial (patchVertex p v x) (p.1 - 2) =
      rightPosition initial v (maxTime initial true v) := by
  have hd := delay_patchVertex v x hp
  have hle : (delay (patchVertex p v x)).1 ≤ p.1 - 2 := by
    rw [hd]
    omega
  rw [rightAbsolutePosition, dif_pos hle]
  have hsub : p.1 - 2 - (delay (patchVertex p v x)).1 =
      maxTime initial true v := by
    rw [hd]
    omega
  rw [hsub]
  exact rightPosition_patchVertex_at_maxTime initial v x hp hgroup

theorem patched_positions_reflect_at_group {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p : Fin (parameterCount D H)}
    (l r : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroupL : (delay l).1 + maxTime initial false l + 2 = p.1)
    (hgroupR : (delay r).1 + maxTime initial true r + 2 = p.1)
    (hmax :
      walkMax initial false l + walkMax initial true r = N) :
    rightAbsolutePosition initial (patchVertex p r x) (p.1 - 2) =
      GamblerWalk.reflect
        (leftAbsolutePosition initial (patchVertex p l x) (p.1 - 2)) := by
  rw [rightAbsolutePosition_patchVertex_at_group initial r x hp hgroupR,
    leftAbsolutePosition_patchVertex_at_group initial l x hp hgroupL]
  apply Fin.ext
  rw [GamblerWalk.reflect_val]
  have hl := position_maxTime initial false l
  have hr := position_maxTime initial true r
  simp only [Bool.false_eq_true, ↓reduceIte] at hl
  simp only [↓reduceIte] at hr
  omega

theorem patched_success_disjoint {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (hN : 0 < N)
    {p : Fin (parameterCount D H)}
    (l r : Vertex (parameterCount D H) (alphabetSize S D))
    (x : Suffix (parameterCount D H) (alphabetSize S D) p)
    (hp : 2 ≤ p.1)
    (hgroupL : (delay l).1 + maxTime initial false l + 2 = p.1)
    (hgroupR : (delay r).1 + maxTime initial true r + 2 = p.1)
    (hmax : walkMax initial false l + walkMax initial true r = N) :
    ¬(leftSuccessful initial (patchVertex p l x) ∧
      rightSuccessful initial (patchVertex p r x)) := by
  let l' := patchVertex p l x
  let r' := patchVertex p r x
  let t := p.1 - 2
  have hdl : delay l' = delay l := delay_patchVertex l x hp
  have hdr : delay r' = delay r := delay_patchVertex r x hp
  have htL : (delay l').1 ≤ t := by
    dsimp [t]
    rw [hdl]
    omega
  have htR : (delay r').1 ≤ t := by
    dsimp [t]
    rw [hdr]
    omega
  have htBound : t < D + H := by
    have hpBound := p.2
    dsimp [t]
    simp only [parameterCount] at hpBound
    omega
  have hstart :
      rightAbsolutePosition initial r' t =
        GamblerWalk.reflect (leftAbsolutePosition initial l' t) := by
    exact patched_positions_reflect_at_group initial l r x hp hgroupL hgroupR hmax
  have hbits : ∀ a (hta : t ≤ a) (ha : a < D + H),
      bitAt r' ⟨a, ha⟩ = bitAt l' ⟨a, ha⟩ := by
    intro a hta ha
    dsimp [l', r']
    have hpa : p.1 ≤ a + 2 := by
      dsimp [t] at hta
      omega
    exact (bitAt_patchVertex_eq l r x ⟨a, ha⟩ hpa).symm
  rintro ⟨hleft, hright⟩
  let TL := (delay l').1 + H
  let TR := (delay r').1 + H
  have htTL : t ≤ TL := by
    have hτ := maxTime_lt initial false l
    dsimp [TL, t]
    rw [hdl]
    omega
  have htTR : t ≤ TR := by
    have hτ := maxTime_lt initial true r
    dsimp [TR, t]
    rw [hdr]
    omega
  have hTLBound : TL ≤ D + H := by
    have hd := (delay l).2
    dsimp [TL]
    rw [hdl]
    omega
  have hTRBound : TR ≤ D + H := by
    have hd := (delay r).2
    dsimp [TR]
    rw [hdr]
    omega
  have hleft0 : leftAbsolutePosition initial l' TL = 0 := by
    dsimp [TL]
    rw [leftAbsolutePosition_horizon]
    exact leftSuccessful_position_H initial l' hleft
  have hright0 : rightAbsolutePosition initial r' TR = 0 := by
    dsimp [TR]
    rw [rightAbsolutePosition_horizon]
    exact rightSuccessful_position_H initial r' hright
  by_cases horder : TL ≤ TR
  · have hcomp := absolute_positions_reflect_of_common_bits initial l' r' t
      (TL - t) htL htR (by omega) hstart hbits
    have heq : t + (TL - t) = TL := Nat.add_sub_of_le htTL
    have hcompTL :
        rightAbsolutePosition initial r' TL =
          GamblerWalk.reflect (leftAbsolutePosition initial l' TL) := by
      rwa [heq] at hcomp
    have hrightTop : rightAbsolutePosition initial r' TL =
        (⟨N, by omega⟩ : GamblerWalk.State N) := by
      rw [hcompTL, hleft0]
      exact GamblerWalk.reflect_zero N
    have hTL_le_horizon : TL ≤ (delay r').1 + H := by
      change TL ≤ TR
      exact horder
    have hposTop := rightPosition_H_eq_top_of_absolute_eq_top initial r' TL
      (htR.trans htTL) hTL_le_horizon hrightTop
    have hposZero := rightSuccessful_position_H initial r' hright
    have hz : (0 : GamblerWalk.State N) = ⟨N, by omega⟩ :=
      hposZero.symm.trans hposTop
    have := congrArg Fin.val hz
    simp at this
    omega
  · have horder' : TR ≤ TL := by omega
    have hcomp := absolute_positions_reflect_of_common_bits initial l' r' t
      (TR - t) htL htR (by omega) hstart hbits
    have heq : t + (TR - t) = TR := Nat.add_sub_of_le htTR
    have hcompTR :
        rightAbsolutePosition initial r' TR =
          GamblerWalk.reflect (leftAbsolutePosition initial l' TR) := by
      rwa [heq] at hcomp
    have hleftTop : leftAbsolutePosition initial l' TR =
        (⟨N, by omega⟩ : GamblerWalk.State N) := by
      have href := congrArg (GamblerWalk.reflect (N := N))
        (hright0.symm.trans hcompTR)
      simpa using href.symm
    have hTR_le_horizon : TR ≤ (delay l').1 + H := by
      change TR ≤ TL
      exact horder'
    have hposTop := leftPosition_H_eq_top_of_absolute_eq_top initial l' TR
      (htL.trans htTR) hTR_le_horizon hleftTop
    have hposZero := leftSuccessful_position_H initial l' hleft
    have hz : (0 : GamblerWalk.State N) = ⟨N, by omega⟩ :=
      hposZero.symm.trans hposTop
    have := congrArg Fin.val hz
    simp at this
    omega

@[simp] theorem visitedValues_right_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    visitedValues initial true (flipVertex v) = visitedValues initial false v := by
  classical
  simp [visitedValues]

@[simp] theorem visitedValues_left_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    visitedValues initial false (flipVertex v) = visitedValues initial true v := by
  rw [← visitedValues_right_flipVertex initial (flipVertex v), flipVertex_flipVertex]

@[simp] theorem walkMax_right_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    walkMax initial true (flipVertex v) = walkMax initial false v := by
  unfold walkMax
  apply Nat.le_antisymm
  · apply Finset.max'_le
    intro y hy
    rw [visitedValues_right_flipVertex] at hy
    exact Finset.le_max' _ _ hy
  · apply Finset.max'_le
    intro y hy
    rw [← visitedValues_right_flipVertex initial v] at hy
    exact Finset.le_max' _ _ hy

@[simp] theorem walkMax_left_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    walkMax initial false (flipVertex v) = walkMax initial true v := by
  rw [← walkMax_right_flipVertex initial (flipVertex v), flipVertex_flipVertex]

@[simp] theorem maxTime_right_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    maxTime initial true (flipVertex v) = maxTime initial false v := by
  apply Nat.le_antisymm
  · let t := maxTime initial false v
    have hs : t < H + 1 ∧ (leftPosition initial v t).1 = walkMax initial false v := by
      exact Nat.find_spec (exists_time_walkMax initial false v)
    have hs' : t < H + 1 ∧
        (rightPosition initial (flipVertex v) t).1 =
          walkMax initial true (flipVertex v) := by
      simpa using hs
    exact Nat.find_min' (exists_time_walkMax initial true (flipVertex v)) hs'
  · let t := maxTime initial true (flipVertex v)
    have hs : t < H + 1 ∧
        (rightPosition initial (flipVertex v) t).1 =
          walkMax initial true (flipVertex v) := by
      exact Nat.find_spec (exists_time_walkMax initial true (flipVertex v))
    have hs' : t < H + 1 ∧
        (leftPosition initial v t).1 = walkMax initial false v := by
      simpa using hs
    exact Nat.find_min' (exists_time_walkMax initial false v) hs'

@[simp] theorem maxTime_left_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    maxTime initial false (flipVertex v) = maxTime initial true v := by
  rw [← maxTime_right_flipVertex initial (flipVertex v), flipVertex_flipVertex]

@[simp] theorem absoluteMaxTime_right_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    absoluteMaxTime initial true (flipVertex v) = absoluteMaxTime initial false v := by
  simp [absoluteMaxTime]

@[simp] theorem absoluteMaxTime_left_flipVertex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    absoluteMaxTime initial false (flipVertex v) = absoluteMaxTime initial true v := by
  simp [absoluteMaxTime]

noncomputable def leftClass {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ) :
    Finset (Vertex (parameterCount D H) (alphabetSize S D)) := by
  classical
  exact Finset.univ.filter fun v ↦
    leftSuccessful initial v ∧ walkMax initial false v = j ∧
      absoluteMaxTime initial false v = t

noncomputable def rightClass {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ) :
    Finset (Vertex (parameterCount D H) (alphabetSize S D)) := by
  classical
  exact Finset.univ.filter fun v ↦
    rightSuccessful initial v ∧ walkMax initial true v = j ∧
      absoluteMaxTime initial true v = t

@[simp] theorem flipVertex_mem_rightClass_iff {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (v : Vertex (parameterCount D H) (alphabetSize S D)) :
    flipVertex v ∈ rightClass initial j t ↔ v ∈ leftClass initial j t := by
  simp [rightClass, leftClass]

noncomputable def leftClassEquivRightClass {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ) :
    {v // v ∈ leftClass (D := D) (H := H) initial j t} ≃
      {v // v ∈ rightClass (D := D) (H := H) initial j t} :=
  Equiv.subtypeEquiv (flipVertexEquiv S D H) fun v ↦ by
    exact (flipVertex_mem_rightClass_iff initial j t v).symm

theorem card_leftClass_eq_card_rightClass {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ) :
    (leftClass (D := D) (H := H) initial j t).card =
      (rightClass (D := D) (H := H) initial j t).card := by
  simpa using Fintype.card_congr
    (leftClassEquivRightClass (D := D) (H := H) initial j t)

abbrev maxLabel (N : ℕ) := Fin (N - 1)

def maxLabelValue {N : ℕ} (j : maxLabel N) : ℕ := j.1 + 1

theorem maxLabelValue_pos {N : ℕ} (j : maxLabel N) : 0 < maxLabelValue j := by
  simp [maxLabelValue]

theorem maxLabelValue_lt {N : ℕ} (hN : 0 < N) (j : maxLabel N) :
    maxLabelValue j < N := by
  have hj := j.2
  simp only [maxLabel, maxLabelValue] at *
  omega

noncomputable def classPairSize {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j : maxLabel N) (t : ℕ) : ℕ :=
  min (leftClass (D := D) (H := H) initial (maxLabelValue j) t).card
    (rightClass (D := D) (H := H) initial (N - maxLabelValue j) t).card

abbrev GroupPairIndex {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H)) :=
  { z : Sigma fun j : maxLabel N =>
      Fin (classPairSize (D := D) (H := H) initial j (p.1 - 2)) //
    H + 2 ≤ p.1 ∧ p.1 < D + 2 }

noncomputable def leftPairEndpoint {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    Vertex (parameterCount D H) (alphabetSize S D) :=
  (Finset.minPairing
    (leftClass (D := D) (H := H) initial (maxLabelValue z.1.1) (p.1 - 2))
    (rightClass (D := D) (H := H) initial (N - maxLabelValue z.1.1) (p.1 - 2))
    z.1.2).1.1

noncomputable def rightPairEndpoint {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    Vertex (parameterCount D H) (alphabetSize S D) :=
  (Finset.minPairing
    (leftClass (D := D) (H := H) initial (maxLabelValue z.1.1) (p.1 - 2))
    (rightClass (D := D) (H := H) initial (N - maxLabelValue z.1.1) (p.1 - 2))
    z.1.2).2.1

theorem leftPairEndpoint_mem {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    leftPairEndpoint initial p z ∈
      leftClass (D := D) (H := H) initial (maxLabelValue z.1.1) (p.1 - 2) :=
  (Finset.minPairing
    (leftClass (D := D) (H := H) initial (maxLabelValue z.1.1) (p.1 - 2))
    (rightClass (D := D) (H := H) initial (N - maxLabelValue z.1.1) (p.1 - 2))
    z.1.2).1.2

theorem rightPairEndpoint_mem {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    rightPairEndpoint initial p z ∈
      rightClass (D := D) (H := H) initial
        (N - maxLabelValue z.1.1) (p.1 - 2) :=
  (Finset.minPairing
    (leftClass (D := D) (H := H) initial (maxLabelValue z.1.1) (p.1 - 2))
    (rightClass (D := D) (H := H) initial (N - maxLabelValue z.1.1) (p.1 - 2))
    z.1.2).2.2

theorem leftPairEndpoint_properties {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    leftSuccessful initial (leftPairEndpoint initial p z) ∧
      walkMax initial false (leftPairEndpoint initial p z) = maxLabelValue z.1.1 ∧
      absoluteMaxTime initial false (leftPairEndpoint initial p z) = p.1 - 2 := by
  simpa [leftClass] using leftPairEndpoint_mem initial p z

theorem rightPairEndpoint_properties {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (z : GroupPairIndex initial p) :
    rightSuccessful initial (rightPairEndpoint initial p z) ∧
      walkMax initial true (rightPairEndpoint initial p z) =
        N - maxLabelValue z.1.1 ∧
      absoluteMaxTime initial true (rightPairEndpoint initial p z) = p.1 - 2 := by
  simpa [rightClass] using rightPairEndpoint_mem initial p z

theorem leftPairEndpoint_injective {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p q : Fin (parameterCount D H)}
    {z : GroupPairIndex initial p} {w : GroupPairIndex initial q}
    (h : leftPairEndpoint initial p z = leftPairEndpoint initial q w) :
    p = q ∧ HEq z w := by
  have hzprop := leftPairEndpoint_properties initial p z
  have hwprop := leftPairEndpoint_properties initial q w
  have hj : maxLabelValue z.1.1 = maxLabelValue w.1.1 := by
    rw [← hzprop.2.1, ← hwprop.2.1]
    exact congrArg (walkMax initial false) h
  have ht : p.1 - 2 = q.1 - 2 := by
    rw [← hzprop.2.2, ← hwprop.2.2]
    exact congrArg (absoluteMaxTime initial false) h
  have hp2 : 2 ≤ p.1 := le_trans (by omega) z.2.1
  have hq2 : 2 ≤ q.1 := le_trans (by omega) w.2.1
  have hpq : p = q := by
    apply Fin.ext
    omega
  subst q
  refine ⟨rfl, ?_⟩
  rcases z with ⟨⟨j, i⟩, hzvalid⟩
  rcases w with ⟨⟨k, u⟩, hwvalid⟩
  have hjk : j = k := by
    apply Fin.ext
    simp [maxLabelValue] at hj
    omega
  subst k
  have hiSubtype :
      (Finset.minPairing
        (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
        (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
        i).1 =
      (Finset.minPairing
        (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
        (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
        u).1 := by
    apply Subtype.ext
    exact h
  have hi : i = u :=
    Finset.minPairing_left_injective
      (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
      (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
      hiSubtype
  subst u
  rfl

theorem rightPairEndpoint_injective {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N)
    {p q : Fin (parameterCount D H)}
    {z : GroupPairIndex initial p} {w : GroupPairIndex initial q}
    (h : rightPairEndpoint initial p z = rightPairEndpoint initial q w) :
    p = q ∧ HEq z w := by
  have hzprop := rightPairEndpoint_properties initial p z
  have hwprop := rightPairEndpoint_properties initial q w
  have hjcomp :
      N - maxLabelValue z.1.1 = N - maxLabelValue w.1.1 := by
    rw [← hzprop.2.1, ← hwprop.2.1]
    exact congrArg (walkMax initial true) h
  have hjz : maxLabelValue z.1.1 < N := by
    have hj := z.1.1.2
    simp only [maxLabel, maxLabelValue] at *
    omega
  have hjw : maxLabelValue w.1.1 < N := by
    have hj := w.1.1.2
    simp only [maxLabel, maxLabelValue] at *
    omega
  have hj : maxLabelValue z.1.1 = maxLabelValue w.1.1 := by omega
  have ht : p.1 - 2 = q.1 - 2 := by
    rw [← hzprop.2.2, ← hwprop.2.2]
    exact congrArg (absoluteMaxTime initial true) h
  have hp2 : 2 ≤ p.1 := le_trans (by omega) z.2.1
  have hq2 : 2 ≤ q.1 := le_trans (by omega) w.2.1
  have hpq : p = q := by
    apply Fin.ext
    omega
  subst q
  refine ⟨rfl, ?_⟩
  rcases z with ⟨⟨j, i⟩, hzvalid⟩
  rcases w with ⟨⟨k, u⟩, hwvalid⟩
  have hjk : j = k := by
    apply Fin.ext
    simp [maxLabelValue] at hj
    omega
  subst k
  have hiSubtype :
      (Finset.minPairing
        (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
        (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
        i).2 =
      (Finset.minPairing
        (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
        (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
        u).2 := by
    apply Subtype.ext
    exact h
  have hi : i = u :=
    Finset.minPairing_right_injective
      (leftClass (D := D) (H := H) initial (maxLabelValue j) (p.1 - 2))
      (rightClass (D := D) (H := H) initial (N - maxLabelValue j) (p.1 - 2))
      hiSubtype
  subst u
  rfl

noncomputable def groupIndexEquiv {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H)) :
    Fin (Fintype.card (GroupPairIndex initial p)) ≃ GroupPairIndex initial p :=
  (Fintype.equivFin (GroupPairIndex initial p)).symm

theorem card_groupPairIndex_of_valid {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (hpLower : H + 2 ≤ p.1) (hpUpper : p.1 < D + 2) :
    Fintype.card (GroupPairIndex initial p) =
      ∑ j : maxLabel N, classPairSize (D := D) (H := H) initial j (p.1 - 2) := by
  let e : GroupPairIndex initial p ≃
      (Sigma fun j : maxLabel N =>
        Fin (classPairSize (D := D) (H := H) initial j (p.1 - 2))) := {
    toFun := fun z ↦ z.1
    invFun := fun z ↦ ⟨z, hpLower, hpUpper⟩
    left_inv := fun z ↦ by rfl
    right_inv := fun z ↦ by rfl }
  calc
    Fintype.card (GroupPairIndex initial p) =
        Fintype.card (Sigma fun j : maxLabel N =>
          Fin (classPairSize (D := D) (H := H) initial j (p.1 - 2))) :=
      Fintype.card_congr e
    _ = ∑ j : maxLabel N, classPairSize (D := D) (H := H) initial j (p.1 - 2) := by
      simp [Fintype.card_sigma]

theorem card_groupPairIndex_of_not_valid {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (p : Fin (parameterCount D H))
    (hp : ¬(H + 2 ≤ p.1 ∧ p.1 < D + 2)) :
    Fintype.card (GroupPairIndex initial p) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro z
  exact hp z.2

theorem central_classPairSize_sum_le_multiplicity_sum {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) :
    (∑ p in (Finset.univ : Finset (Fin (parameterCount D H))).filter
          (fun p ↦ H + 2 ≤ p.1 ∧ p.1 < D + 2),
        ∑ j : maxLabel N,
          classPairSize (D := D) (H := H) initial j (p.1 - 2)) ≤
      ∑ p : Fin (parameterCount D H),
        Fintype.card (GroupPairIndex initial p) := by
  calc
    (∑ p in (Finset.univ : Finset (Fin (parameterCount D H))).filter
          (fun p ↦ H + 2 ≤ p.1 ∧ p.1 < D + 2),
        ∑ j : maxLabel N,
          classPairSize (D := D) (H := H) initial j (p.1 - 2)) =
      ∑ p in (Finset.univ : Finset (Fin (parameterCount D H))).filter
          (fun p ↦ H + 2 ≤ p.1 ∧ p.1 < D + 2),
        Fintype.card (GroupPairIndex initial p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hv := (Finset.mem_filter.mp hp).2
      exact (card_groupPairIndex_of_valid initial p hv.1 hv.2).symm
    _ ≤ ∑ p : Fin (parameterCount D H),
        Fintype.card (GroupPairIndex initial p) :=
      Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _

noncomputable def paperIndexedData {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (hN : 0 < N) :
    IndexedBlueprintData (parameterCount D H) (alphabetSize S D) where
  edgeMultiplicity := fun p ↦ Fintype.card (GroupPairIndex initial p)
  left := fun p i ↦ leftPairEndpoint initial p (groupIndexEquiv initial p i)
  right := fun p i ↦ rightPairEndpoint initial p (groupIndexEquiv initial p i)
  left_injective := by
    intro p q i j h
    obtain ⟨hpq, hzw⟩ := leftPairEndpoint_injective initial h
    subst q
    have hzw' : groupIndexEquiv initial p i = groupIndexEquiv initial p j :=
      eq_of_heq hzw
    have hij : i = j := (groupIndexEquiv initial p).injective hzw'
    exact ⟨rfl, heq_of_eq hij⟩
  right_injective := by
    intro p q i j h
    obtain ⟨hpq, hzw⟩ := rightPairEndpoint_injective initial h
    subst q
    have hzw' : groupIndexEquiv initial p i = groupIndexEquiv initial p j :=
      eq_of_heq hzw
    have hij : i = j := (groupIndexEquiv initial p).injective hzw'
    exact ⟨rfl, heq_of_eq hij⟩
  ban := by
    intro p i x
    let z := groupIndexEquiv initial p i
    let l := leftPairEndpoint initial p z
    let r := rightPairEndpoint initial p z
    have hp : 2 ≤ p.1 := le_trans (by omega) z.2.1
    have hlprop := leftPairEndpoint_properties initial p z
    have hrprop := rightPairEndpoint_properties initial p z
    have hgL : (delay l).1 + maxTime initial false l + 2 = p.1 := by
      have ht := hlprop.2.2
      change absoluteMaxTime initial false l = p.1 - 2 at ht
      simp only [absoluteMaxTime] at ht
      omega
    have hgR : (delay r).1 + maxTime initial true r + 2 = p.1 := by
      have ht := hrprop.2.2
      change absoluteMaxTime initial true r = p.1 - 2 at ht
      simp only [absoluteMaxTime] at ht
      omega
    have hjlt : maxLabelValue z.1.1 < N := maxLabelValue_lt hN z.1.1
    have hmax : walkMax initial false l + walkMax initial true r = N := by
      rw [hlprop.2.1, hrprop.2.1]
      omega
    have hdisjoint := patched_success_disjoint initial hN l r x hp hgL hgR hmax
    by_cases hleft : leftSuccessful initial (patchVertex p l x)
    · right
      intro hmatched
      apply hdisjoint ⟨hleft, ?_⟩
      rcases hmatched with ⟨q, j, hj⟩
      have hs := (rightPairEndpoint_properties initial q
        (groupIndexEquiv initial q j)).1
      exact hj ▸ hs
    · left
      intro hmatched
      exact hleft (by
        rcases hmatched with ⟨q, j, hj⟩
        have hs := (leftPairEndpoint_properties initial q
          (groupIndexEquiv initial q j)).1
        exact hj ▸ hs)

noncomputable def paperBlueprint {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (hN : 0 < N)
    (hS : 0 < S) (hD : 0 < D) : SimpleProperBlueprint :=
  (paperIndexedData (D := D) (H := H) initial hN).toBlueprint
    (by simp [parameterCount])
    (by rw [alphabetSize_eq]; positivity)

theorem paperBlueprint_value_lower {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (hN : 0 < N)
    (hS : 0 < S) (hD : 0 < D) :
    (((∑ p, (paperIndexedData (D := D) (H := H) initial hN).edgeMultiplicity p : ℕ) : ℝ) /
        ((alphabetSize S D) ^ (parameterCount D H) : ℕ)) ≤
      (paperBlueprint (H := H) initial hN hS hD).value := by
  exact (paperIndexedData (D := D) (H := H) initial hN).indexedDensity_le_value
    (by simp [parameterCount]) (by rw [alphabetSize_eq]; positivity)

end PaperWalkEncoding
