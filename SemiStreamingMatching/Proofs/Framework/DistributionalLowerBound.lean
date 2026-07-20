import SemiStreamingMatching.Definitions.Algorithm

open scoped BigOperators

namespace Formal.Streaming

variable {L R : Type*} [Fintype L] [Fintype R]
  [DecidableEq L] [DecidableEq R]

structure FiniteGraphDistribution (L R : Type*)
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] where
  Sample : Type
  [sampleFintype : Fintype Sample]
  [sampleNonempty : Nonempty Sample]
  graph : Sample → BipartiteGraph L R
  stream : ∀ x, (graph x).EdgeStream

namespace FiniteGraphDistribution

instance (D : FiniteGraphDistribution L R) : Fintype D.Sample := D.sampleFintype
instance (D : FiniteGraphDistribution L R) : Nonempty D.Sample := D.sampleNonempty

noncomputable def successIndicator (D : FiniteGraphDistribution L R)
    (A : OnePassAlgorithm L R) (ρ : ℚ) (x : D.Sample) : ℚ :=
  by
    classical
    exact if A.SucceedsOn ρ (D.graph x) (D.stream x) then 1 else 0

noncomputable def successMass (D : FiniteGraphDistribution L R)
    (A : OnePassAlgorithm L R) (ρ : ℚ) : ℚ :=
  ∑ x : D.Sample, D.successIndicator A ρ x

noncomputable def successProbability (D : FiniteGraphDistribution L R)
    (A : OnePassAlgorithm L R) (ρ : ℚ) : ℚ :=
  D.successMass A ρ / Fintype.card D.Sample

def IsHardForBits (D : FiniteGraphDistribution L R)
    (ρ p : ℚ) (s : ℕ) : Prop :=
  ∀ A : OnePassAlgorithm L R, A.UsesBits s →
    D.successMass A ρ ≤ p * Fintype.card D.Sample

theorem exists_input_randomized_success_le
    (D : FiniteGraphDistribution L R) {ρ p : ℚ} {s : ℕ}
    (hD : D.IsHardForBits ρ p s)
    (A : RandomizedOnePassAlgorithm L R) (hA : A.UsesBits s) :
    ∃ x : D.Sample,
      A.successProbability ρ (D.graph x) (D.stream x) ≤ p := by
  classical
  let seedMass : D.Sample → ℚ := fun x ↦
    ∑ ξ : A.Seed, D.successIndicator (A.fixSeed ξ) ρ x
  have hseed (ξ : A.Seed) :
      D.successMass (A.fixSeed ξ) ρ ≤ p * Fintype.card D.Sample :=
    hD (A.fixSeed ξ) (A.fixSeed_usesBits hA ξ)
  have htotal :
      (∑ x : D.Sample, seedMass x) ≤
        Fintype.card A.Seed * (p * Fintype.card D.Sample) := by
    calc
      (∑ x : D.Sample, seedMass x) =
          ∑ ξ : A.Seed, D.successMass (A.fixSeed ξ) ρ := by
        simp only [seedMass, successMass]
        rw [Finset.sum_comm]
      _ ≤ ∑ _ξ : A.Seed, p * Fintype.card D.Sample :=
        Finset.sum_le_sum fun ξ _ ↦ hseed ξ
      _ = Fintype.card A.Seed * (p * Fintype.card D.Sample) := by
        simp
  have hexists : ∃ x : D.Sample,
      seedMass x ≤ p * Fintype.card A.Seed := by
    by_contra hnot
    push_neg at hnot
    have hstrict :
        (∑ _x : D.Sample, p * Fintype.card A.Seed) <
          ∑ x : D.Sample, seedMass x := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro x _
        exact hnot x
    have hconst :
        (∑ _x : D.Sample, p * Fintype.card A.Seed) =
          Fintype.card A.Seed * (p * Fintype.card D.Sample) := by
      simp
      ring
    rw [hconst] at hstrict
    exact (not_lt_of_ge htotal) hstrict
  obtain ⟨x, hx⟩ := hexists
  refine ⟨x, ?_⟩
  have hmass :
      ((A.successfulSeeds ρ (D.graph x) (D.stream x)).card : ℚ) = seedMass x := by
    simp [seedMass, successIndicator,
      RandomizedOnePassAlgorithm.successfulSeeds]
  rw [RandomizedOnePassAlgorithm.successProbability, hmass]
  apply (div_le_iff (show (0 : ℚ) < Fintype.card A.Seed by exact_mod_cast Fintype.card_pos)).2
  simpa [mul_comm] using hx

end FiniteGraphDistribution

end Formal.Streaming
