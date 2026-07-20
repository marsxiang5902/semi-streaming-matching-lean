import SemiStreamingMatching.Proofs.Framework.Communication
import SemiStreamingMatching.Proofs.Framework.DistributionalLowerBound

namespace Formal.Streaming

open scoped BigOperators

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

noncomputable def simulateProtocol (P : ℕ) (A : OnePassAlgorithm L R) :
    BlackboardProtocol P L R where
  Message := A.State
  messageFintype := A.stateFintype
  initial := A.init
  send := fun _p block history =>
    A.runFrom (history.getLastD A.init) block.toList
  output := fun history => A.output (history.getLastD A.init)

theorem simulateProtocol_playFrom_last {P : ℕ} (A : OnePassAlgorithm L R)
    (I : EdgePartition P L R) (players : List (Fin P))
    (history : List A.State) :
    ((simulateProtocol P A).playFrom I players history).getLastD A.init =
      A.runFrom (history.getLastD A.init) (players.bind I.blockOrder) := by
  classical
  induction players generalizing history with
  | nil => simp [BlackboardProtocol.playFrom, OnePassAlgorithm.runFrom]
  | cons p ps ih =>
      change
        ((simulateProtocol P A).playFrom I ps
          (history ++
            [A.runFrom (history.getLastD A.init) (I.block p).toList])).getLastD A.init =
          A.runFrom (history.getLastD A.init)
            (I.blockOrder p ++ ps.bind I.blockOrder)
      rw [ih]
      simp only [List.getLastD_concat]
      rw [← OnePassAlgorithm.runFrom_append]
      rfl

theorem simulateProtocol_finalState {P : ℕ} (A : OnePassAlgorithm L R)
    (I : EdgePartition P L R) :
    ((simulateProtocol P A).transcript I).getLastD A.init =
      A.run I.streamOrder := by
  classical
  rw [BlackboardProtocol.transcript, simulateProtocol_playFrom_last]
  rfl

theorem simulateProtocol_result {P : ℕ} (A : OnePassAlgorithm L R)
    (I : EdgePartition P L R) :
    (simulateProtocol P A).result I = A.result I.streamOrder := by
  classical
  unfold BlackboardProtocol.result OnePassAlgorithm.result
  change
    A.output (((simulateProtocol P A).transcript I).getLastD A.init) =
      A.output (A.run I.streamOrder)
  rw [simulateProtocol_finalState]

theorem simulateProtocol_usesCommunication {P s : ℕ}
    {A : OnePassAlgorithm L R} (hA : A.UsesBits s) :
    (simulateProtocol P A).UsesCommunication s := by
  exact hA

theorem simulateProtocol_succeedsOn_iff {P : ℕ}
    [Fintype L] [Fintype R] (A : OnePassAlgorithm L R)
    (ρ : ℚ) (I : EdgePartition P L R) :
    (simulateProtocol P A).SucceedsOn ρ I ↔
      A.SucceedsOn ρ I.graph I.stream := by
  classical
  unfold BlackboardProtocol.SucceedsOn OnePassAlgorithm.SucceedsOn
  rw [simulateProtocol_result]
  rfl

noncomputable def simulateSeedProtocol (P : ℕ)
    (A : RandomizedOnePassAlgorithm L R) (ξ : A.Seed) :
    BlackboardProtocol P L R :=
  simulateProtocol P (A.fixSeed ξ)

theorem simulateSeedProtocol_usesCommunication {P s : ℕ}
    {A : RandomizedOnePassAlgorithm L R} (hA : A.UsesBits s) (ξ : A.Seed) :
    (simulateSeedProtocol P A ξ).UsesCommunication s :=
  simulateProtocol_usesCommunication (A.fixSeed_usesBits hA ξ)

theorem simulateSeedProtocol_result {P : ℕ}
    (A : RandomizedOnePassAlgorithm L R) (ξ : A.Seed)
    (I : EdgePartition P L R) :
    (simulateSeedProtocol P A ξ).result I =
      (A.fixSeed ξ).result I.streamOrder :=
  simulateProtocol_result (A.fixSeed ξ) I

noncomputable def simulatedProtocolSuccessProbability {P : ℕ}
    [Fintype L] [Fintype R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (I : EdgePartition P L R) : ℚ := by
  classical
  exact
    ((Finset.univ.filter fun ξ : A.Seed =>
      (simulateSeedProtocol P A ξ).SucceedsOn ρ I).card : ℚ) /
      Fintype.card A.Seed

theorem simulatedProtocol_successProbability_eq {P : ℕ}
    [Fintype L] [Fintype R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (I : EdgePartition P L R) :
    simulatedProtocolSuccessProbability A ρ I =
      A.successProbability ρ I.graph I.stream := by
  classical
  unfold simulatedProtocolSuccessProbability
  unfold RandomizedOnePassAlgorithm.successProbability
  have hsets :
      (Finset.univ.filter fun ξ : A.Seed =>
        (simulateSeedProtocol P A ξ).SucceedsOn ρ I) =
        A.successfulSeeds ρ I.graph I.stream := by
    ext ξ
    simp only [RandomizedOnePassAlgorithm.successfulSeeds,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact simulateProtocol_succeedsOn_iff (A.fixSeed ξ) ρ I
  rw [hsets]

theorem simulateProtocol_distributional_success_eq
    {P : ℕ} [Fintype L] [Fintype R]
    {Ω : Type*} [Fintype Ω]
    (D : FiniteDistribution Ω) (input : Ω → EdgePartition P L R)
    (A : OnePassAlgorithm L R) (ρ : ℚ) :
    protocolSuccessProbability D input (simulateProtocol P A) ρ =
      D.probability
        (fun ω => A.SucceedsOn ρ (input ω).graph (input ω).stream) := by
  classical
  unfold protocolSuccessProbability FiniteDistribution.probability
  have hsets :
      Finset.univ.filter
          (fun ω => (simulateProtocol P A).SucceedsOn ρ (input ω)) =
        Finset.univ.filter
          (fun ω => A.SucceedsOn ρ (input ω).graph (input ω).stream) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact simulateProtocol_succeedsOn_iff A ρ (input ω)
  rw [hsets]

theorem proposition_2_1_deterministic
    {P s : ℕ} [Fintype L] [Fintype R]
    {Ω : Type*} [Fintype Ω]
    (D : FiniteDistribution Ω) (input : Ω → EdgePartition P L R)
    (ρ p : ℚ)
    (hcommunication :
      ∀ prot : BlackboardProtocol P L R, prot.UsesCommunication s →
        protocolSuccessProbability D input prot ρ ≤ p)
    (A : OnePassAlgorithm L R) (hspace : A.UsesBits s) :
    D.probability
        (fun ω => A.SucceedsOn ρ (input ω).graph (input ω).stream) ≤ p := by
  rw [← simulateProtocol_distributional_success_eq D input A ρ]
  exact hcommunication (simulateProtocol P A)
    (simulateProtocol_usesCommunication hspace)

structure FinitePartitionDistribution (P : ℕ) (L R : Type*)
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] where
  Sample : Type
  [sampleFintype : Fintype Sample]
  [sampleNonempty : Nonempty Sample]
  input : Sample → EdgePartition P L R

namespace FinitePartitionDistribution

variable {P : ℕ} [Fintype L] [Fintype R]

instance (D : FinitePartitionDistribution P L R) : Fintype D.Sample :=
  D.sampleFintype

instance (D : FinitePartitionDistribution P L R) : Nonempty D.Sample :=
  D.sampleNonempty

noncomputable def toGraphDistribution (D : FinitePartitionDistribution P L R) :
    FiniteGraphDistribution L R where
  Sample := D.Sample
  sampleFintype := D.sampleFintype
  sampleNonempty := D.sampleNonempty
  graph := fun x => (D.input x).graph
  stream := fun x => (D.input x).stream

noncomputable def protocolSuccessMass (D : FinitePartitionDistribution P L R)
    (prot : BlackboardProtocol P L R) (ρ : ℚ) : ℚ := by
  classical
  exact ∑ x : D.Sample, if prot.SucceedsOn ρ (D.input x) then 1 else 0

def IsHardForCommunication (D : FinitePartitionDistribution P L R)
    (ρ p : ℚ) (s : ℕ) : Prop :=
  ∀ prot : BlackboardProtocol P L R, prot.UsesCommunication s →
    D.protocolSuccessMass prot ρ ≤ p * Fintype.card D.Sample

theorem toGraphDistribution_isHardForBits
    (D : FinitePartitionDistribution P L R) {ρ p : ℚ} {s : ℕ}
    (hD : D.IsHardForCommunication ρ p s) :
    D.toGraphDistribution.IsHardForBits ρ p s := by
  classical
  intro A hA
  have hsim := hD (simulateProtocol P A)
    (simulateProtocol_usesCommunication hA)
  unfold protocolSuccessMass at hsim
  change
    (∑ x : D.Sample,
      if A.SucceedsOn ρ (D.input x).graph (D.input x).stream then 1 else 0) ≤
        p * Fintype.card D.Sample
  calc
    _ = ∑ x : D.Sample,
        if (simulateProtocol P A).SucceedsOn ρ (D.input x) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show
        A.SucceedsOn ρ (D.input x).graph (D.input x).stream ↔
          (simulateProtocol P A).SucceedsOn ρ (D.input x) from
        (simulateProtocol_succeedsOn_iff A ρ (D.input x)).symm]
    _ ≤ p * Fintype.card D.Sample := hsim

theorem proposition_2_1
    (D : FinitePartitionDistribution P L R) {ρ p : ℚ} {s : ℕ}
    (hD : D.IsHardForCommunication ρ p s)
    (A : RandomizedOnePassAlgorithm L R) (hA : A.UsesBits s) :
    ∃ x : D.Sample,
      A.successProbability ρ (D.input x).graph (D.input x).stream ≤ p := by
  exact FiniteGraphDistribution.exists_input_randomized_success_le
    D.toGraphDistribution (D.toGraphDistribution_isHardForBits hD) A hA

end FinitePartitionDistribution

end Formal.Streaming
