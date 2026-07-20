import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

abbrev Vertex (P C : ℕ) := Fin P → Fin C

abbrev Suffix (P C : ℕ) (p : Fin P) :=
  (i : Fin P) → p ≤ i → Fin C

def patchVertex {P C : ℕ} (p : Fin P) (v : Vertex P C) (x : Suffix P C p) :
    Vertex P C :=
  fun i =>
    if h : p ≤ i then
      x i h
    else
      v i

abbrev Edge (P C : ℕ) := Vertex P C × Vertex P C

abbrev EdgeFamily (P C : ℕ) := Fin P → Finset (Edge P C)

def leftMatched {P C : ℕ} (E : EdgeFamily P C) (l : Vertex P C) : Prop :=
  ∃ p : Fin P, ∃ r : Vertex P C, (l, r) ∈ E p

def rightMatched {P C : ℕ} (E : EdgeFamily P C) (r : Vertex P C) : Prop :=
  ∃ p : Fin P, ∃ l : Vertex P C, (l, r) ∈ E p

structure SimpleProperBlueprint where
  P : ℕ
  hP : 0 < P
  C : ℕ
  hC : 0 < C
  E : EdgeFamily P C
  left_matching :
    ∀ {p q : Fin P} {l : Vertex P C} {r1 r2 : Vertex P C},
      (l, r1) ∈ E p → (l, r2) ∈ E q → p = q ∧ r1 = r2
  right_matching :
    ∀ {p q : Fin P} {l1 l2 : Vertex P C} {r : Vertex P C},
      (l1, r) ∈ E p → (l2, r) ∈ E q → p = q ∧ l1 = l2
  bans :
    ∀ {p : Fin P} {l r : Vertex P C},
      (l, r) ∈ E p →
      ∀ x : Suffix P C p,
        ¬ leftMatched E (patchVertex p l x) ∨ ¬ rightMatched E (patchVertex p r x)

abbrev SimpleProperBlueprint.EdgeOver (B : SimpleProperBlueprint) :=
  Sigma (fun _ : Fin B.P => Edge B.P B.C)

noncomputable def SimpleProperBlueprint.edgeCount (B : SimpleProperBlueprint) : ℕ := by
  classical
  exact Fintype.card { e : B.EdgeOver // e.2 ∈ B.E e.1 }

noncomputable def SimpleProperBlueprint.vertexCount (B : SimpleProperBlueprint) : ℕ :=
  Fintype.card (Vertex B.P B.C)

noncomputable def SimpleProperBlueprint.value (B : SimpleProperBlueprint) : ℝ :=
  (B.edgeCount : ℝ) / (B.vertexCount : ℝ)

theorem value_nonneg (B : SimpleProperBlueprint) : 0 ≤ B.value := by
  rw [SimpleProperBlueprint.value]
  exact div_nonneg (Nat.cast_nonneg B.edgeCount) (Nat.cast_nonneg B.vertexCount)

theorem value_le_one (B : SimpleProperBlueprint) : B.value ≤ 1 := by
  classical
  let leftOf : { e : B.EdgeOver // e.2 ∈ B.E e.1 } → Vertex B.P B.C := fun e => e.1.2.1
  have hleft_inj : Function.Injective leftOf := by
    intro e₁ e₂ h
    rcases e₁ with ⟨⟨p1, e1⟩, hp1⟩
    rcases e₂ with ⟨⟨p2, e2⟩, hp2⟩
    rcases e1 with ⟨l1, r1⟩
    rcases e2 with ⟨l2, r2⟩
    simp [leftOf] at h
    subst h
    rcases B.left_matching (p := p1) (q := p2) (l := l1) (r1 := r1) (r2 := r2) hp1 hp2 with ⟨hp, hr⟩
    subst hp
    subst hr
    rfl
  have hcard : B.edgeCount ≤ B.vertexCount := by
    unfold SimpleProperBlueprint.edgeCount SimpleProperBlueprint.vertexCount
    exact Fintype.card_le_of_injective leftOf hleft_inj
  have hnum_le_den : (B.edgeCount : ℝ) ≤ B.vertexCount := by
    exact_mod_cast hcard
  have hden_pos_nat : 0 < B.vertexCount := by
    unfold SimpleProperBlueprint.vertexCount
    exact Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, B.hC⟩⟩
  have hden_pos : (0 : ℝ) < B.vertexCount := by
    exact_mod_cast hden_pos_nat
  rw [SimpleProperBlueprint.value]
  exact (div_le_iff hden_pos).2 (by simpa using hnum_le_den)

theorem value_mem_Icc (B : SimpleProperBlueprint) : B.value ∈ Set.Icc 0 1 := by
  exact ⟨value_nonneg B, value_le_one B⟩

def zeroBlueprint : SimpleProperBlueprint where
  P := 1
  hP := by decide
  C := 1
  hC := by decide
  E := fun _ => ∅
  left_matching := by
    intro p q l r1 r2 hp _
    simp at hp
  right_matching := by
    intro p q l1 l2 r hp _
    simp at hp
  bans := by
    intro p l r hp x
    simp at hp

theorem zeroBlueprint_value : zeroBlueprint.value = 0 := by
  simp [SimpleProperBlueprint.value, SimpleProperBlueprint.edgeCount,
    SimpleProperBlueprint.vertexCount, zeroBlueprint]

def edge : Edge 1 1 := (fun _ => 0, fun _ => 0)

abbrev halfLeft : Vertex 1 2 := fun _ => 0

abbrev halfRight : Vertex 1 2 := fun _ => 1

abbrev halfEdges : EdgeFamily 1 2 := fun _ => {(halfLeft, halfRight)}

lemma halfLeft_ne_halfRight : halfLeft ≠ halfRight := by
  intro h
  have h01 : (0 : Fin 2) = 1 := by
    simpa [halfLeft, halfRight] using congrArg (fun v => v 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) h01

@[simp] lemma leftMatched_halfEdges_iff (v : Vertex 1 2) :
    leftMatched halfEdges v ↔ v = halfLeft := by
  constructor
  · rintro ⟨p, r, hp⟩
    exact (by
      simpa [halfEdges, halfLeft, halfRight] using hp : v = halfLeft ∧ r = halfRight).1
  · intro hv
    subst hv
    refine ⟨0, halfRight, ?_⟩
    simp [halfEdges, halfLeft, halfRight]

@[simp] lemma rightMatched_halfEdges_iff (v : Vertex 1 2) :
    rightMatched halfEdges v ↔ v = halfRight := by
  constructor
  · rintro ⟨p, l, hp⟩
    exact (by
      simpa [halfEdges, halfLeft, halfRight] using hp : l = halfLeft ∧ v = halfRight).2
  · intro hv
    subst hv
    refine ⟨0, halfLeft, ?_⟩
    simp [halfEdges, halfLeft, halfRight]

lemma patchVertex_fin1_eq {p : Fin 1} {l r : Vertex 1 2} (x : Suffix 1 2 p) :
    patchVertex p l x = patchVertex p r x := by
  ext i
  have hpi : p ≤ i := by
    simp [Subsingleton.elim p i]
  simp [patchVertex, hpi]

def halfBlueprint : SimpleProperBlueprint where
  P := 1
  hP := by decide
  C := 2
  hC := by decide
  E := halfEdges
  left_matching := by
    intro p q l r1 r2 hp hq
    rcases (by simpa [halfEdges, halfLeft, halfRight] using hp :
      l = halfLeft ∧ r1 = halfRight) with ⟨hl, hr1⟩
    rcases (by simpa [halfEdges, halfLeft, halfRight] using hq :
      l = halfLeft ∧ r2 = halfRight) with ⟨_, hr2⟩
    subst l
    subst r1
    subst r2
    exact ⟨Subsingleton.elim p q, rfl⟩
  right_matching := by
    intro p q l1 l2 r hp hq
    rcases (by simpa [halfEdges, halfLeft, halfRight] using hp :
      l1 = halfLeft ∧ r = halfRight) with ⟨hl1, hr⟩
    rcases (by simpa [halfEdges, halfLeft, halfRight] using hq :
      l2 = halfLeft ∧ r = halfRight) with ⟨hl2, _⟩
    subst l1
    subst l2
    subst r
    exact ⟨Subsingleton.elim p q, rfl⟩
  bans := by
    intro p l r hp x
    rcases (by simpa [halfEdges, halfLeft, halfRight] using hp :
      l = halfLeft ∧ r = halfRight) with ⟨hl, hr⟩
    subst l
    subst r
    have hpatch : patchVertex p halfLeft x = patchVertex p halfRight x :=
      patchVertex_fin1_eq x
    by_cases hL : leftMatched halfEdges (patchVertex p halfLeft x)
    · right
      intro hR
      rw [← hpatch] at hR
      have hvL : patchVertex p halfLeft x = halfLeft := by
        simpa using hL
      have hvR : patchVertex p halfLeft x = halfRight := by
        simpa using hR
      exact halfLeft_ne_halfRight (hvL.symm.trans hvR)
    · left
      exact hL
