import SemiStreamingMatching.Proofs.Framework.ERSFamily

namespace Formal.Streaming

def sequenceTail {alpha : Type*} (f : ℕ → alpha) (offset : ℕ) : ℕ → alpha :=
  fun k ↦ f (offset + k)

theorem SizesTendToInfinity.tail {size : ℕ → ℕ}
    (h : SizesTendToInfinity size) (offset : ℕ) :
    SizesTendToInfinity (sequenceTail size offset) := by
  intro N
  obtain ⟨k0, hk0⟩ := h N
  refine ⟨k0, fun k hk ↦ ?_⟩
  exact hk0 (offset + k) (hk.trans (Nat.le_add_left k offset))

theorem DominatesPolylogAlong.tail {size t : ℕ → ℕ}
    (h : DominatesPolylogAlong size t) (offset : ℕ) :
    DominatesPolylogAlong (sequenceTail size offset) (sequenceTail t offset) := by
  intro c exponent
  obtain ⟨k0, hk0⟩ := h c exponent
  refine ⟨k0, fun k hk ↦ ?_⟩
  exact hk0 (offset + k) (hk.trans (Nat.le_add_left k offset))

namespace ERSFamily

namespace DenseERSSequence

variable {C : ℕ}

def tail (F : DenseERSSequence C) (offset : ℕ) : DenseERSSequence C where
  toERSSequence :=
    { n := sequenceTail F.n offset
      r := sequenceTail F.r offset
      t := sequenceTail F.t offset
      host := fun k ↦ F.host (offset + k) }
  relativeLossNumerator := F.relativeLossNumerator
  relativeLossDenominator := F.relativeLossDenominator
  relativeLoss_lt := F.relativeLoss_lt
  matching_dense := fun k ↦ F.matching_dense (offset + k)
  baseSizesGrow := F.baseSizesGrow.tail offset
  multiplicityGrowth := by
    intro P hP
    simpa [ERSSequence.augmentedExpansionSize, sequenceTail] using
      (F.multiplicityGrowth P hP).tail offset

@[simp]
theorem tail_n (F : DenseERSSequence C) (offset k : ℕ) :
    (F.tail offset).n k = F.n (offset + k) := rfl

@[simp]
theorem tail_r (F : DenseERSSequence C) (offset k : ℕ) :
    (F.tail offset).r k = F.r (offset + k) := rfl

@[simp]
theorem tail_t (F : DenseERSSequence C) (offset k : ℕ) :
    (F.tail offset).t k = F.t (offset + k) := rfl

@[simp]
theorem tail_host (F : DenseERSSequence C) (offset k : ℕ) :
    (F.tail offset).host k = F.host (offset + k) := rfl

end DenseERSSequence

end ERSFamily

end Formal.Streaming
