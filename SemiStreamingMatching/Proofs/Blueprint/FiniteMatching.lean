import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Finset

variable {α β : Type*} [Fintype α] [DecidableEq α]

noncomputable def initialEmbedding (s : Finset α) (k : ℕ) (hk : k ≤ s.card) : Fin k ↪ ↥s :=
  (Fin.castLEEmb (by simpa using hk)).toEmbedding.trans
    (Fintype.equivFin ↥s).symm.toEmbedding

theorem initialEmbedding_injective (s : Finset α) (k : ℕ) (hk : k ≤ s.card) :
    Function.Injective (initialEmbedding s k hk) :=
  (initialEmbedding s k hk).injective

noncomputable def minPairing (s : Finset α) (t : Finset β)
    [Fintype β] [DecidableEq β] :
    Fin (min s.card t.card) → ↥s × ↥t :=
  fun i =>
    (initialEmbedding s _ (min_le_left _ _) i,
      initialEmbedding t _ (min_le_right _ _) i)

theorem minPairing_left_injective (s : Finset α) (t : Finset β)
    [Fintype β] [DecidableEq β] :
    Function.Injective (fun i => (minPairing s t i).1) :=
  (initialEmbedding s _ (min_le_left _ _)).injective

theorem minPairing_right_injective (s : Finset α) (t : Finset β)
    [Fintype β] [DecidableEq β] :
    Function.Injective (fun i => (minPairing s t i).2) :=
  (initialEmbedding t _ (min_le_right _ _)).injective

end Finset
