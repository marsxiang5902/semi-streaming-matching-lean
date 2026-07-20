import SemiStreamingMatching.Proofs.Framework.StreamingReduction

namespace Formal.Streaming

namespace BlackboardProtocol

variable {P : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]

theorem UsesCommunication.mono {prot : BlackboardProtocol P L R} {s S : ℕ}
    (h : prot.UsesCommunication s) (hsS : s ≤ S) :
    prot.UsesCommunication S := by
  change Nonempty (prot.Message ↪ BitString S)
  apply Function.Embedding.nonempty_of_card_le
  calc
    Fintype.card prot.Message ≤ 2 ^ s := h.messageCard_le
    _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide) hsS
    _ = Fintype.card (BitString S) := by
      simp [BitString, Fintype.card_fun]

end BlackboardProtocol

namespace FinitePartitionDistribution

variable {P : ℕ} {L R : Type*}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem IsHardForCommunication.mono_bits
    {D : FinitePartitionDistribution P L R} {rho p : ℚ} {s S : ℕ}
    (hD : D.IsHardForCommunication rho p S) (hsS : s ≤ S) :
    D.IsHardForCommunication rho p s := by
  intro prot hprot
  exact hD prot (hprot.mono hsS)

theorem IsHardForCommunication.mono_approximation
    {D : FinitePartitionDistribution P L R} {rho rho' p : ℚ} {s : ℕ}
    (hD : D.IsHardForCommunication rho p s) (hrr' : rho ≤ rho') :
    D.IsHardForCommunication rho' p s := by
  intro prot hprot
  have hbase := hD prot hprot
  unfold FinitePartitionDistribution.protocolSuccessMass at hbase ⊢
  apply le_trans _ hbase
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hx : prot.SucceedsOn rho' (D.input x)
  · have hx' : prot.SucceedsOn rho (D.input x) := by
      refine ⟨hx.1, ?_⟩
      calc
        rho * ((D.input x).graph.matchingNumber : ℚ) ≤
            rho' * ((D.input x).graph.matchingNumber : ℚ) :=
          mul_le_mul_of_nonneg_right hrr' (by positivity)
        _ ≤ ((prot.result (D.input x)).card : ℚ) := hx.2
    simp [hx, hx']
  · simp only [hx, if_false]
    split <;> norm_num

end FinitePartitionDistribution

end Formal.Streaming
