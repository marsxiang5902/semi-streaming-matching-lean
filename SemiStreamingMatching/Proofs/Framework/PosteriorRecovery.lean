import SemiStreamingMatching.Proofs.Framework.SpecialEdgeLowerBound
import Mathlib.Tactic

namespace Formal.Streaming

open scoped BigOperators

namespace UniformPosterior

variable {Ω S E : Type*}
  [Fintype Ω] [Fintype S] [Fintype E]
  [DecidableEq Ω] [DecidableEq S] [DecidableEq E]

def fiber (summary : Ω → S) (s : S) : Finset Ω :=
  Finset.univ.filter fun ω => summary ω = s

noncomputable def presentFiber (summary : Ω → S) (present : Ω → E → Prop)
    (s : S) (e : E) : Finset Ω := by
  classical
  exact (fiber summary s).filter fun ω => present ω e

noncomputable def Belongs (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (s : S) (e : E) : Prop :=
  (1 - η) * (fiber summary s).card ≤
    (presentFiber summary present s e).card

noncomputable def belongingEdges (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (s : S) : Finset E := by
  classical
  exact Finset.univ.filter fun e => Belongs η summary present s e

@[simp]
theorem mem_belongingEdges_iff (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (s : S) (e : E) :
    e ∈ belongingEdges η summary present s ↔
      Belongs η summary present s e := by
  classical
  simp [belongingEdges]

def Feasible (summary : Ω → S) (present : Ω → E → Prop)
    (output : S → Finset E) (ω : Ω) : Prop :=
  ∀ e ∈ output (summary ω), present ω e

def HasNonbelonging (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (output : S → Finset E) (ω : Ω) : Prop :=
  ∃ e ∈ output (summary ω),
    e ∉ belongingEdges η summary present (summary ω)

def HasManyRelevant (summary : Ω → S) (output relevant : S → Finset E)
    (q : ℕ) (ω : Ω) : Prop :=
  q < (output (summary ω) ∩ relevant (summary ω)).card

def HasManyBelongingRelevant (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (relevant : S → Finset E)
    (q : ℕ) (ω : Ω) : Prop :=
  q < (belongingEdges η summary present (summary ω) ∩
    relevant (summary ω)).card

noncomputable def feasibleNonbelongingSamples (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (output : S → Finset E) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω =>
    Feasible summary present output ω ∧
      HasNonbelonging η summary present output ω

noncomputable def manyBelongingRelevantSamples (η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (relevant : S → Finset E)
    (q : ℕ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω =>
    HasManyBelongingRelevant η summary present relevant q ω

noncomputable def feasibleManyRelevantSamples (_η : ℚ) (summary : Ω → S)
    (present : Ω → E → Prop) (output relevant : S → Finset E)
    (q : ℕ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω =>
    Feasible summary present output ω ∧
      HasManyRelevant summary output relevant q ω

private theorem card_eq_sum_fibers (summary : Ω → S) (A : Finset Ω) :
    A.card = ∑ s : S, (A.filter fun ω => summary ω = s).card := by
  exact Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.univ)
    (f := summary) (by simp)

theorem feasible_nonbelonging_card_le
    {η : ℚ} (hη1 : η ≤ 1)
    (summary : Ω → S) (present : Ω → E → Prop)
    (output : S → Finset E) :
    ((feasibleNonbelongingSamples η summary present output).card : ℚ) ≤
      (1 - η) * Fintype.card Ω := by
  classical
  let A := feasibleNonbelongingSamples η summary present output
  have hfiber (s : S) :
      (((A.filter fun ω => summary ω = s).card : ℕ) : ℚ) ≤
        (1 - η) * (fiber summary s).card := by
    by_cases hs : ∃ e ∈ output s,
        e ∉ belongingEdges η summary present s
    · obtain ⟨e, heout, henot⟩ := hs
      have hsubset :
          (A.filter fun ω => summary ω = s) ⊆
            presentFiber summary present s e := by
        intro ω hω
        have hA : ω ∈ A := (Finset.mem_filter.1 hω).1
        have hsum : summary ω = s := (Finset.mem_filter.1 hω).2
        have hfeas : Feasible summary present output ω := by
          simpa [A, feasibleNonbelongingSamples] using
            (Finset.mem_filter.1 hA).2.1
        simp only [presentFiber, Finset.mem_filter, fiber,
          Finset.mem_univ, true_and]
        refine ⟨hsum, ?_⟩
        exact hfeas e (by simpa [hsum] using heout)
      have hcard :
          (A.filter fun ω => summary ω = s).card ≤
            (presentFiber summary present s e).card :=
        Finset.card_le_card hsubset
      have hnotBelongs : ¬ Belongs η summary present s e := by
        simpa using henot
      have hpresent :
          ((presentFiber summary present s e).card : ℚ) <
            (1 - η) * (fiber summary s).card := by
        exact lt_of_not_ge hnotBelongs
      exact le_trans (by exact_mod_cast hcard) hpresent.le
    · have hempty : A.filter (fun ω => summary ω = s) = ∅ := by
        ext ω
        simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
        rintro ⟨hA, hsum⟩
        have hnon : HasNonbelonging η summary present output ω := by
          simpa [A, feasibleNonbelongingSamples] using
            (Finset.mem_filter.1 hA).2.2
        obtain ⟨e, heout, henot⟩ := hnon
        apply hs
        refine ⟨e, ?_, ?_⟩
        · simpa [hsum] using heout
        · simpa [hsum] using henot
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (sub_nonneg.mpr hη1)
        (by positivity : (0 : ℚ) ≤ (fiber summary s).card)
  calc
    (A.card : ℚ) = ∑ s : S,
        (((A.filter fun ω => summary ω = s).card : ℕ) : ℚ) := by
      rw [card_eq_sum_fibers summary A]
      norm_num
    _ ≤ ∑ s : S, (1 - η) * (fiber summary s).card :=
      Finset.sum_le_sum fun s _ => hfiber s
    _ = (1 - η) * ∑ s : S, ((fiber summary s).card : ℚ) := by
      rw [Finset.mul_sum]
    _ = (1 - η) * Fintype.card Ω := by
      congr 1
      have hsum : (∑ s : S, (fiber summary s).card) = Fintype.card Ω := by
        simpa [fiber] using
          (card_eq_sum_fibers summary (Finset.univ : Finset Ω)).symm
      exact_mod_cast hsum

theorem feasible_many_relevant_card_le
    {η β : ℚ} (hη1 : η ≤ 1)
    (summary : Ω → S) (present : Ω → E → Prop)
    (output relevant : S → Finset E) (q : ℕ)
    (hbelong :
      ((manyBelongingRelevantSamples η summary present relevant q).card : ℚ) ≤
        β * Fintype.card Ω) :
    ((feasibleManyRelevantSamples η summary present output relevant q).card : ℚ) ≤
      (1 - η + β) * Fintype.card Ω := by
  classical
  let A := feasibleManyRelevantSamples η summary present output relevant q
  let N := feasibleNonbelongingSamples η summary present output
  let B := manyBelongingRelevantSamples η summary present relevant q
  have hsubset : A ⊆ N ∪ B := by
    intro ω hω
    have hdata := (Finset.mem_filter.1 hω).2
    by_cases hnon : HasNonbelonging η summary present output ω
    · exact Finset.mem_union_left _ (by
        simp only [N, feasibleNonbelongingSamples, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨hdata.1, hnon⟩)
    · apply Finset.mem_union_right
      simp only [B, manyBelongingRelevantSamples, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have houtsub : output (summary ω) ⊆
          belongingEdges η summary present (summary ω) := by
        intro e he
        by_contra henot
        exact hnon ⟨e, he, henot⟩
      have hinter :
          output (summary ω) ∩ relevant (summary ω) ⊆
            belongingEdges η summary present (summary ω) ∩
              relevant (summary ω) := by
        exact Finset.inter_subset_inter houtsub (fun _ h => h)
      have hcard := Finset.card_le_card hinter
      exact lt_of_lt_of_le hdata.2 hcard
  have hcardUnion : A.card ≤ N.card + B.card :=
    le_trans (Finset.card_le_card hsubset) (Finset.card_union_le N B)
  have hnon := feasible_nonbelonging_card_le hη1 summary present output
  have hbelong' : (B.card : ℚ) ≤ β * Fintype.card Ω := by
    simpa [B] using hbelong
  calc
    (A.card : ℚ) ≤ (N.card : ℚ) + (B.card : ℚ) := by
      exact_mod_cast hcardUnion
    _ ≤ (1 - η) * Fintype.card Ω + β * Fintype.card Ω :=
      add_le_add (by simpa [N] using hnon) hbelong'
    _ = (1 - η + β) * Fintype.card Ω := by ring

end UniformPosterior

end Formal.Streaming
