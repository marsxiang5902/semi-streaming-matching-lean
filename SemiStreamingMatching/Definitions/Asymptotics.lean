import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Formal.Streaming

def IsSemiStreamingSpace (space : ℕ → ℕ) : Prop :=
  ∃ c k n₀ : ℕ, 0 < c ∧
    ∀ n, n₀ ≤ n →
      space n ≤ c * n * (Nat.log 2 n + 1) ^ k

def DominatesPolylog (t : ℕ → ℕ) : Prop :=
  ∀ c k : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    c * (Nat.log 2 n + 1) ^ k ≤ t n

def DominatesPolylogAlong (size t : ℕ → ℕ) : Prop :=
  ∀ c k : ℕ, ∃ k₀ : ℕ, ∀ i, k₀ ≤ i →
    c * (Nat.log 2 (size i) + 1) ^ k ≤ t i

def SizesTendToInfinity (size : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ k₀ : ℕ, ∀ i, k₀ ≤ i → N ≤ size i

theorem semiStreaming_eventually_le_n_mul
    {space t : ℕ → ℕ} (hspace : IsSemiStreamingSpace space)
    (ht : DominatesPolylog t) (q : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → q * space n ≤ n * t n := by
  rcases hspace with ⟨c, k, nspace, _hc, hspace⟩
  obtain ⟨nhost, hhost⟩ := ht (q * c) k
  refine ⟨max nspace nhost, fun n hn ↦ ?_⟩
  have hs := hspace n (le_trans (le_max_left _ _) hn)
  have hh := hhost n (le_trans (le_max_right _ _) hn)
  calc
    q * space n ≤ q * (c * n * (Nat.log 2 n + 1) ^ k) :=
      Nat.mul_le_mul_left q hs
    _ = n * (q * c * (Nat.log 2 n + 1) ^ k) := by ring
    _ ≤ n * t n := Nat.mul_le_mul_left n hh

theorem semiStreaming_eventually_add_le_n_mul
    {space t : ℕ → ℕ} (hspace : IsSemiStreamingSpace space)
    (ht : DominatesPolylog t) (q a : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → q * space n + a * n ≤ n * (t n + a) := by
  obtain ⟨n₀, h⟩ := semiStreaming_eventually_le_n_mul hspace ht q
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have := h n hn
  nlinarith

theorem semiStreaming_along_eventually_le_size_mul
    {space size t : ℕ → ℕ} (hspace : IsSemiStreamingSpace space)
    (hsize : SizesTendToInfinity size)
    (ht : DominatesPolylogAlong size t) (q : ℕ) :
    ∃ k₀ : ℕ, ∀ i, k₀ ≤ i →
      q * space (size i) ≤ size i * t i := by
  rcases hspace with ⟨c, k, nspace, _hc, hspace⟩
  obtain ⟨kgrowth, hgrowth⟩ := ht (q * c) k
  obtain ⟨ksize, hsize⟩ := hsize nspace
  refine ⟨max ksize kgrowth, fun i hi ↦ ?_⟩
  have hs := hspace (size i) (hsize i (le_trans (le_max_left _ _) hi))
  have ht' := hgrowth i (le_trans (le_max_right _ _) hi)
  calc
    q * space (size i) ≤
        q * (c * size i * (Nat.log 2 (size i) + 1) ^ k) :=
      Nat.mul_le_mul_left q hs
    _ = size i * (q * c * (Nat.log 2 (size i) + 1) ^ k) := by ring
    _ ≤ size i * t i := Nat.mul_le_mul_left (size i) ht'

end Formal.Streaming
