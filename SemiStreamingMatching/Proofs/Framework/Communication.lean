import SemiStreamingMatching.Definitions.Algorithm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Union

namespace Formal.Streaming

open scoped BigOperators

variable {L R : Type*}

structure EdgePartition (P : ℕ) (L R : Type*) [DecidableEq L] [DecidableEq R] where
  block : Fin P → Finset (Edge L R)
  disjoint : ∀ ⦃p q : Fin P⦄, p ≠ q → Disjoint (block p) (block q)

namespace EdgePartition

variable {P : ℕ} [DecidableEq L] [DecidableEq R]

def edgeSet (I : EdgePartition P L R) : Finset (Edge L R) :=
  Finset.univ.biUnion I.block

def graph (I : EdgePartition P L R) : BipartiteGraph L R :=
  ⟨I.edgeSet⟩

noncomputable def blockOrder (I : EdgePartition P L R) (p : Fin P) :
    List (Edge L R) :=
  (I.block p).toList

@[simp]
theorem blockOrder_nodup (I : EdgePartition P L R) (p : Fin P) :
    (I.blockOrder p).Nodup := by
  classical
  exact (I.block p).nodup_toList

@[simp]
theorem blockOrder_toFinset (I : EdgePartition P L R) (p : Fin P) :
    (I.blockOrder p).toFinset = I.block p := by
  classical
  exact (I.block p).toList_toFinset

noncomputable def streamOrder (I : EdgePartition P L R) : List (Edge L R) :=
  (List.finRange P).bind I.blockOrder

theorem streamOrder_toFinset (I : EdgePartition P L R) :
    I.streamOrder.toFinset = I.edgeSet := by
  classical
  ext e
  simp [streamOrder, edgeSet, blockOrder]

theorem streamOrder_nodup (I : EdgePartition P L R) :
    I.streamOrder.Nodup := by
  classical
  rw [streamOrder, List.nodup_bind]
  refine ⟨?_, ?_⟩
  · intro p _hp
    exact I.blockOrder_nodup p
  · refine (List.nodup_finRange P).imp ?_
    intro p q hpq
    rw [List.disjoint_left]
    intro e hep heq
    have hep' : e ∈ I.block p := by
      simpa [blockOrder] using hep
    have heq' : e ∈ I.block q := by
      simpa [blockOrder] using heq
    exact (Finset.disjoint_left.mp (I.disjoint hpq)) hep' heq'

noncomputable def stream (I : EdgePartition P L R) : I.graph.EdgeStream where
  order := I.streamOrder
  nodup := I.streamOrder_nodup
  covers := I.streamOrder_toFinset

end EdgePartition

structure BlackboardProtocol (P : ℕ) (L R : Type*)
    [DecidableEq L] [DecidableEq R] where
  Message : Type
  [messageFintype : Fintype Message]
  initial : Message
  send : Fin P → Finset (Edge L R) → List Message → Message
  output : List Message → Finset (Edge L R)

namespace BlackboardProtocol

variable {P : ℕ} [DecidableEq L] [DecidableEq R]

instance (prot : BlackboardProtocol P L R) : Fintype prot.Message :=
  prot.messageFintype

def playFrom (prot : BlackboardProtocol P L R) (I : EdgePartition P L R) :
    List (Fin P) → List prot.Message → List prot.Message
  | [], history => history
  | p :: ps, history =>
      prot.playFrom I ps (history ++ [prot.send p (I.block p) history])

def transcript (prot : BlackboardProtocol P L R) (I : EdgePartition P L R) :
    List prot.Message :=
  prot.playFrom I (List.finRange P) [prot.initial]

def result (prot : BlackboardProtocol P L R) (I : EdgePartition P L R) :
    Finset (Edge L R) :=
  prot.output (prot.transcript I)

@[simp]
theorem playFrom_nil (prot : BlackboardProtocol P L R) (I : EdgePartition P L R)
    (history : List prot.Message) :
    prot.playFrom I [] history = history :=
  rfl

theorem playFrom_cons (prot : BlackboardProtocol P L R) (I : EdgePartition P L R)
    (p : Fin P) (ps : List (Fin P)) (history : List prot.Message) :
    prot.playFrom I (p :: ps) history =
      prot.playFrom I ps (history ++ [prot.send p (I.block p) history]) :=
  rfl

theorem playFrom_length (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (players : List (Fin P))
    (history : List prot.Message) :
    (prot.playFrom I players history).length = history.length + players.length := by
  induction players generalizing history with
  | nil => simp [playFrom]
  | cons p ps ih =>
      change
        (prot.playFrom I ps
          (history ++ [prot.send p (I.block p) history])).length =
          history.length + (p :: ps).length
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem transcript_length (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) :
    (prot.transcript I).length = P + 1 := by
  rw [transcript, playFrom_length]
  simp [Nat.add_comm]

def MessageEncoding (prot : BlackboardProtocol P L R) (s : ℕ) :=
  prot.Message ↪ BitString s

def UsesCommunication (prot : BlackboardProtocol P L R) (s : ℕ) : Prop :=
  Nonempty (prot.MessageEncoding s)

theorem UsesCommunication.messageCard_le {prot : BlackboardProtocol P L R} {s : ℕ}
    (h : prot.UsesCommunication s) : Fintype.card prot.Message ≤ 2 ^ s := by
  obtain ⟨enc⟩ := h
  simpa [MessageEncoding, BitString] using Fintype.card_le_of_embedding enc

def SucceedsOn [Fintype L] [Fintype R]
    (prot : BlackboardProtocol P L R) (ρ : ℚ) (I : EdgePartition P L R) : Prop :=
  OnePassAlgorithm.MeetsApproximation ρ I.graph (prot.result I)

end BlackboardProtocol

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℚ
  nonnegative : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

noncomputable def probability (D : FiniteDistribution Ω) (event : Ω → Prop) : ℚ := by
  classical
  exact ∑ ω in Finset.univ.filter event, D.weight ω

theorem probability_nonnegative (D : FiniteDistribution Ω) (event : Ω → Prop) :
    0 ≤ D.probability event := by
  classical
  unfold probability
  exact Finset.sum_nonneg fun ω _ => D.nonnegative ω

@[simp]
theorem probability_true (D : FiniteDistribution Ω) :
    D.probability (fun _ => True) = 1 := by
  classical
  simpa [probability] using D.total

@[simp]
theorem probability_false (D : FiniteDistribution Ω) :
    D.probability (fun _ => False) = 0 := by
  classical
  simp [probability]

end FiniteDistribution

noncomputable def protocolSuccessProbability
    {P : ℕ} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {Ω : Type*} [Fintype Ω]
    (D : FiniteDistribution Ω) (input : Ω → EdgePartition P L R)
    (prot : BlackboardProtocol P L R) (ρ : ℚ) : ℚ :=
  D.probability (fun ω => prot.SucceedsOn ρ (input ω))

end Formal.Streaming
