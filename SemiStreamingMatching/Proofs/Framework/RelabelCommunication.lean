import SemiStreamingMatching.Proofs.Framework.Relabel
import SemiStreamingMatching.Proofs.Framework.StreamingReduction

namespace Formal.Streaming

open scoped BigOperators

namespace BipartiteGraph

variable {L R L' R' : Type*}
  [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
  [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

@[simp]
theorem relabelEdges_symm_relabelEdges (eL : L ≃ L') (eR : R ≃ R')
    (E : Finset (Edge L R)) :
    relabelEdges eL.symm eR.symm (relabelEdges eL eR E) = E := by
  ext z
  simp [mem_relabelEdges_iff]

@[simp]
theorem relabelEdges_relabelEdges_symm (eL : L ≃ L') (eR : R ≃ R')
    (E : Finset (Edge L' R')) :
    relabelEdges eL eR (relabelEdges eL.symm eR.symm E) = E := by
  ext z
  simp [mem_relabelEdges_iff]

@[simp]
theorem relabel_symm_relabel (G : BipartiteGraph L R)
    (eL : L ≃ L') (eR : R ≃ R') :
    (G.relabel eL eR).relabel eL.symm eR.symm = G := by
  apply BipartiteGraph.ext
  exact relabelEdges_symm_relabelEdges eL eR G.edges

@[simp]
theorem relabel_relabel_symm (G : BipartiteGraph L' R')
    (eL : L ≃ L') (eR : R ≃ R') :
    (G.relabel eL.symm eR.symm).relabel eL eR = G := by
  apply BipartiteGraph.ext
  exact relabelEdges_relabelEdges_symm eL eR G.edges

theorem isMatching_relabel_iff (G : BipartiteGraph L R)
    (M : Finset (Edge L R)) (eL : L ≃ L') (eR : R ≃ R') :
    (G.relabel eL eR).IsMatching (relabelEdges eL eR M) ↔
      G.IsMatching M := by
  constructor
  · intro hM
    have hback := hM.relabel eL.symm eR.symm
    simpa using hback
  · intro hM
    exact hM.relabel eL eR

theorem meetsApproximation_relabel_iff (ρ : ℚ) (G : BipartiteGraph L R)
    (M : Finset (Edge L R)) (eL : L ≃ L') (eR : R ≃ R') :
    OnePassAlgorithm.MeetsApproximation ρ (G.relabel eL eR)
        (relabelEdges eL eR M) ↔
      OnePassAlgorithm.MeetsApproximation ρ G M := by
  unfold OnePassAlgorithm.MeetsApproximation
  rw [isMatching_relabel_iff, matchingNumber_relabel, relabelEdges_card]

end BipartiteGraph

namespace EdgePartition

variable {P : ℕ} {L R L' R' : Type*}
  [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

@[ext]
theorem ext {I J : EdgePartition P L R} (h : I.block = J.block) : I = J := by
  cases I with
  | mk blockI disjointI =>
      cases J with
      | mk blockJ disjointJ =>
          cases h
          rfl

def relabel (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R') :
    EdgePartition P L' R' where
  block p := BipartiteGraph.relabelEdges eL eR (I.block p)
  disjoint := by
    intro p q hpq
    rw [Finset.disjoint_left]
    intro z hzp hzq
    rw [BipartiteGraph.mem_relabelEdges_iff] at hzp hzq
    exact (Finset.disjoint_left.mp (I.disjoint hpq)) hzp hzq

@[simp]
theorem relabel_block (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') (p : Fin P) :
    (I.relabel eL eR).block p =
      BipartiteGraph.relabelEdges eL eR (I.block p) :=
  rfl

@[simp]
theorem relabel_block_card (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') (p : Fin P) :
    ((I.relabel eL eR).block p).card = (I.block p).card := by
  exact BipartiteGraph.relabelEdges_card eL eR (I.block p)

theorem edgeSet_relabel (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') :
    (I.relabel eL eR).edgeSet =
      BipartiteGraph.relabelEdges eL eR I.edgeSet := by
  ext z
  simp only [edgeSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
    relabel_block, BipartiteGraph.mem_relabelEdges_iff]

@[simp]
theorem edgeSet_relabel_card (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') :
    (I.relabel eL eR).edgeSet.card = I.edgeSet.card := by
  rw [edgeSet_relabel, BipartiteGraph.relabelEdges_card]

theorem graph_relabel (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') :
    (I.relabel eL eR).graph = I.graph.relabel eL eR := by
  apply BipartiteGraph.ext
  exact edgeSet_relabel I eL eR

@[simp]
theorem relabel_symm_relabel (I : EdgePartition P L R) (eL : L ≃ L')
    (eR : R ≃ R') :
    (I.relabel eL eR).relabel eL.symm eR.symm = I := by
  apply EdgePartition.ext
  funext p
  exact BipartiteGraph.relabelEdges_symm_relabelEdges eL eR (I.block p)

@[simp]
theorem relabel_relabel_symm (I : EdgePartition P L' R') (eL : L ≃ L')
    (eR : R ≃ R') :
    (I.relabel eL.symm eR.symm).relabel eL eR = I := by
  apply EdgePartition.ext
  funext p
  exact BipartiteGraph.relabelEdges_relabelEdges_symm eL eR (I.block p)

end EdgePartition

namespace BlackboardProtocol

variable {P : ℕ} {L R L' R' : Type*}
  [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
  [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

def relabel (prot : BlackboardProtocol P L R)
    (eL : L ≃ L') (eR : R ≃ R') : BlackboardProtocol P L' R' where
  Message := prot.Message
  messageFintype := prot.messageFintype
  initial := prot.initial
  send p block history :=
    prot.send p (BipartiteGraph.relabelEdges eL.symm eR.symm block) history
  output history :=
    BipartiteGraph.relabelEdges eL eR (prot.output history)

@[simp]
theorem relabel_initial (prot : BlackboardProtocol P L R)
    (eL : L ≃ L') (eR : R ≃ R') :
    (prot.relabel eL eR).initial = prot.initial :=
  rfl

@[simp]
theorem relabel_send_block (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R')
    (p : Fin P) (history : List prot.Message) :
    (prot.relabel eL eR).send p ((I.relabel eL eR).block p) history =
      prot.send p (I.block p) history := by
  simp [relabel]

theorem playFrom_relabel (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R')
    (players : List (Fin P)) (history : List prot.Message) :
    (prot.relabel eL eR).playFrom (I.relabel eL eR) players history =
      prot.playFrom I players history := by
  induction players generalizing history with
  | nil => rfl
  | cons p ps ih =>
      simp only [BlackboardProtocol.playFrom]
      dsimp only [relabel, EdgePartition.relabel]
      rw [BipartiteGraph.relabelEdges_symm_relabelEdges]
      exact ih _

theorem transcript_relabel (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R') :
    (prot.relabel eL eR).transcript (I.relabel eL eR) =
      prot.transcript I := by
  unfold transcript
  exact playFrom_relabel prot I eL eR _ _

theorem result_relabel (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R') :
    (prot.relabel eL eR).result (I.relabel eL eR) =
      BipartiteGraph.relabelEdges eL eR (prot.result I) := by
  unfold result
  rw [transcript_relabel]
  rfl

@[simp]
theorem usesCommunication_relabel_iff (prot : BlackboardProtocol P L R)
    (eL : L ≃ L') (eR : R ≃ R') (s : ℕ) :
    (prot.relabel eL eR).UsesCommunication s ↔ prot.UsesCommunication s :=
  Iff.rfl

theorem succeedsOn_relabel_iff (prot : BlackboardProtocol P L R)
    (ρ : ℚ) (I : EdgePartition P L R) (eL : L ≃ L') (eR : R ≃ R') :
    (prot.relabel eL eR).SucceedsOn ρ (I.relabel eL eR) ↔
      prot.SucceedsOn ρ I := by
  unfold SucceedsOn
  rw [EdgePartition.graph_relabel, result_relabel]
  exact BipartiteGraph.meetsApproximation_relabel_iff ρ I.graph
    (prot.result I) eL eR

end BlackboardProtocol

namespace FinitePartitionDistribution

variable {P : ℕ} {L R L' R' : Type*}
  [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
  [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

def relabel (D : FinitePartitionDistribution P L R)
    (eL : L ≃ L') (eR : R ≃ R') : FinitePartitionDistribution P L' R' where
  Sample := D.Sample
  sampleFintype := D.sampleFintype
  sampleNonempty := D.sampleNonempty
  input x := (D.input x).relabel eL eR

@[simp]
theorem relabel_input (D : FinitePartitionDistribution P L R)
    (eL : L ≃ L') (eR : R ≃ R') (x : D.Sample) :
    (D.relabel eL eR).input x = (D.input x).relabel eL eR :=
  rfl

theorem protocolSuccessMass_relabel
    (D : FinitePartitionDistribution P L R)
    (prot : BlackboardProtocol P L R) (ρ : ℚ)
    (eL : L ≃ L') (eR : R ≃ R') :
    (D.relabel eL eR).protocolSuccessMass (prot.relabel eL eR) ρ =
      D.protocolSuccessMass prot ρ := by
  classical
  unfold protocolSuccessMass
  apply Finset.sum_congr rfl
  intro x _hx
  rw [show
    (prot.relabel eL eR).SucceedsOn ρ
        ((D.relabel eL eR).input x) ↔
      prot.SucceedsOn ρ (D.input x) from
    BlackboardProtocol.succeedsOn_relabel_iff prot ρ (D.input x) eL eR]

theorem isHardForCommunication_relabel_iff
    (D : FinitePartitionDistribution P L R)
    (eL : L ≃ L') (eR : R ≃ R') (ρ p : ℚ) (s : ℕ) :
    (D.relabel eL eR).IsHardForCommunication ρ p s ↔
      D.IsHardForCommunication ρ p s := by
  classical
  constructor
  · intro hD prot hprot
    have hpull :
        (prot.relabel eL eR).UsesCommunication s :=
      (BlackboardProtocol.usesCommunication_relabel_iff prot eL eR s).2 hprot
    have h := hD (prot.relabel eL eR) hpull
    rwa [protocolSuccessMass_relabel] at h
  · intro hD prot hprot
    let pullback := prot.relabel eL.symm eR.symm
    have hpull : pullback.UsesCommunication s := by
      exact (BlackboardProtocol.usesCommunication_relabel_iff
        prot eL.symm eR.symm s).2 hprot
    have h := hD pullback hpull
    unfold protocolSuccessMass at h ⊢
    calc
      (∑ x : D.Sample,
          if prot.SucceedsOn ρ ((D.input x).relabel eL eR) then 1 else 0) =
          ∑ x : D.Sample,
            if pullback.SucceedsOn ρ (D.input x) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hx :
            pullback.SucceedsOn ρ (D.input x) ↔
              prot.SucceedsOn ρ ((D.input x).relabel eL eR) := by
          simpa [pullback] using
            (BlackboardProtocol.succeedsOn_relabel_iff prot ρ
              ((D.input x).relabel eL eR) eL.symm eR.symm)
        rw [← hx]
      _ ≤ p * Fintype.card D.Sample := h

theorem IsHardForCommunication.relabel
    {D : FinitePartitionDistribution P L R} {ρ p : ℚ} {s : ℕ}
    (hD : D.IsHardForCommunication ρ p s)
    (eL : L ≃ L') (eR : R ≃ R') :
    (D.relabel eL eR).IsHardForCommunication ρ p s :=
  (isHardForCommunication_relabel_iff D eL eR ρ p s).2 hD

end FinitePartitionDistribution

end Formal.Streaming
