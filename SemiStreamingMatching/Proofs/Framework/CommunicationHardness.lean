import SemiStreamingMatching.Proofs.Framework.Compression
import SemiStreamingMatching.Proofs.Framework.HardDistribution
import SemiStreamingMatching.Proofs.Framework.PosteriorRecovery
import SemiStreamingMatching.Proofs.Framework.SpecialEdges

open scoped BigOperators

namespace Formal.Streaming

namespace BlackboardProtocol

variable {P : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]

def conditionalMessageScheme (prot : BlackboardProtocol P L R) (p : Fin P)
    (history : List prot.Message) :
    Compression.Scheme (Edge L R) prot.Message :=
  fun privateEdges ↦ prot.send p privateEdges history

theorem conditionalMessageScheme_card_le
    (prot : BlackboardProtocol P L R) {s : ℕ}
    (hprot : prot.UsesCommunication s) :
    Fintype.card prot.Message ≤ 2 ^ s :=
  hprot.messageCard_le

abbrev TranscriptCode (prot : BlackboardProtocol P L R) :=
  Fin (P + 1) → prot.Message

def transcriptCode (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) : prot.TranscriptCode :=
  fun i ↦ (prot.transcript I).get
    (Fin.cast (prot.transcript_length I).symm i)

def outputFromTranscriptCode (prot : BlackboardProtocol P L R)
    (code : prot.TranscriptCode) : Finset (Edge L R) :=
  prot.output (List.ofFn code)

@[simp]
theorem ofFn_transcriptCode (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) :
    List.ofFn (prot.transcriptCode I) = prot.transcript I := by
  apply (List.ext_get_iff).2
  constructor
  · simp [transcriptCode, prot.transcript_length I]
  · intro n hleft hright
    simp [transcriptCode]

@[simp]
theorem outputFromTranscriptCode_transcriptCode
    (prot : BlackboardProtocol P L R) (I : EdgePartition P L R) :
    prot.outputFromTranscriptCode (prot.transcriptCode I) = prot.result I := by
  unfold outputFromTranscriptCode BlackboardProtocol.result
  rw [ofFn_transcriptCode]

theorem transcriptCode_eq_iff (prot : BlackboardProtocol P L R)
    (I I' : EdgePartition P L R) :
    prot.transcriptCode I = prot.transcriptCode I' ↔
      prot.transcript I = prot.transcript I' := by
  constructor
  · intro h
    have hf : List.ofFn (prot.transcriptCode I) =
        List.ofFn (prot.transcriptCode I') := congrArg List.ofFn h
    simpa only [ofFn_transcriptCode] using hf
  · intro h
    apply List.ofFn_injective
    simpa only [ofFn_transcriptCode] using h

def generatedMessages (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) :
    List (Fin P) → List prot.Message → List prot.Message
  | [], _history => []
  | p :: players, history =>
      let msg := prot.send p (I.block p) history
      msg :: prot.generatedMessages I players (history ++ [msg])

theorem playFrom_eq_append_generatedMessages
    (prot : BlackboardProtocol P L R) (I : EdgePartition P L R)
    (players : List (Fin P)) (history : List prot.Message) :
    prot.playFrom I players history =
      history ++ prot.generatedMessages I players history := by
  induction players generalizing history with
  | nil => simp [BlackboardProtocol.playFrom, generatedMessages]
  | cons p players ih =>
      rw [BlackboardProtocol.playFrom_cons, ih]
      simp [generatedMessages, List.append_assoc]

theorem playFrom_congr_blocks
    (prot : BlackboardProtocol P L R) (candidate reference : EdgePartition P L R)
    (players : List (Fin P)) (history : List prot.Message)
    (hblocks : ∀ p ∈ players, candidate.block p = reference.block p) :
    prot.playFrom candidate players history =
      prot.playFrom reference players history := by
  induction players generalizing history with
  | nil => rfl
  | cons p players ih =>
      rw [BlackboardProtocol.playFrom_cons, BlackboardProtocol.playFrom_cons,
        hblocks p (by simp)]
      apply ih
      intro q hq
      exact hblocks q (by simp [hq])

theorem val_lt_of_mem_take_finRange {n k : ℕ} (i : Fin n)
    (hi : i ∈ (List.finRange n).take k) : i.val < k := by
  obtain ⟨j, hj⟩ := List.get_of_mem hi
  have hjk : j.val < k :=
    lt_of_lt_of_le j.isLt (List.length_take_le k (List.finRange n))
  have hjn : j.val < (List.finRange n).length := by
    have hjlt : j.val < min k (List.finRange n).length := by
      simpa only [List.length_take] using j.isLt
    exact lt_of_lt_of_le hjlt (Nat.min_le_right _ _)
  have hget := List.get_take (List.finRange n) hjn hjk
  have heq : (⟨j.val, by simpa using hjn⟩ : Fin n) = i := by
    calc
      (⟨j.val, by simpa using hjn⟩ : Fin n) =
          (List.finRange n).get ⟨j.val, hjn⟩ := by
            symm
            exact List.get_finRange hjn
      _ = ((List.finRange n).take k).get j := hget
      _ = i := hj
  simpa [← heq] using hjk

def FollowsReference (prot : BlackboardProtocol P L R)
    (candidate reference : EdgePartition P L R) :
    List (Fin P) → List prot.Message → Prop
  | [], _history => True
  | p :: players, history =>
      let msg := prot.send p (reference.block p) history
      prot.send p (candidate.block p) history = msg ∧
        prot.FollowsReference candidate reference players (history ++ [msg])

theorem generatedMessages_eq_iff_followsReference
    (prot : BlackboardProtocol P L R)
    (candidate reference : EdgePartition P L R)
    (players : List (Fin P)) (history : List prot.Message) :
    prot.generatedMessages candidate players history =
        prot.generatedMessages reference players history ↔
      prot.FollowsReference candidate reference players history := by
  induction players generalizing history with
  | nil => simp [generatedMessages, FollowsReference]
  | cons p players ih =>
      simp only [generatedMessages, FollowsReference, List.cons.injEq]
      constructor
      · rintro ⟨hmsg, htail⟩
        refine ⟨hmsg, ?_⟩
        simpa [hmsg] using
          (ih (history ++ [prot.send p (reference.block p) history])).1
            (by simpa [hmsg] using htail)
      · rintro ⟨hmsg, htail⟩
        refine ⟨hmsg, ?_⟩
        simpa [hmsg] using
          (ih (history ++ [prot.send p (reference.block p) history])).2 htail

theorem transcript_eq_iff_followsReference
    (prot : BlackboardProtocol P L R)
    (candidate reference : EdgePartition P L R) :
    prot.transcript candidate = prot.transcript reference ↔
      prot.FollowsReference candidate reference (List.finRange P)
        [prot.initial] := by
  rw [BlackboardProtocol.transcript, BlackboardProtocol.transcript,
    playFrom_eq_append_generatedMessages,
    playFrom_eq_append_generatedMessages]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
  exact generatedMessages_eq_iff_followsReference prot candidate reference
    (List.finRange P) [prot.initial]

theorem followsReference_iff_forall_position
    (prot : BlackboardProtocol P L R)
    (candidate reference : EdgePartition P L R)
    (players : List (Fin P)) (history : List prot.Message) :
    prot.FollowsReference candidate reference players history ↔
      ∀ n : Fin players.length,
        prot.send (players.get n) (candidate.block (players.get n))
            (prot.playFrom reference (players.take n.val) history) =
          prot.send (players.get n) (reference.block (players.get n))
            (prot.playFrom reference (players.take n.val) history) := by
  induction players generalizing history with
  | nil => simp [FollowsReference]
  | cons p players ih =>
      simp only [FollowsReference]
      constructor
      · rintro ⟨hhead, htail⟩ n
        refine Fin.cases hhead ?_ n
        intro k
        simpa [ih, BlackboardProtocol.playFrom] using
          (ih (history ++ [prot.send p (reference.block p) history])).1
            htail k
      · intro hall
        refine ⟨?_, ?_⟩
        · simpa using hall ⟨0, by simp⟩
        · apply
            (ih (history ++
              [prot.send p (reference.block p) history])).2
          intro k
          simpa [BlackboardProtocol.playFrom] using hall k.succ

def historyBefore (prot : BlackboardProtocol P L R)
    (I : EdgePartition P L R) (p : Fin P) : List prot.Message :=
  prot.playFrom I ((List.finRange P).take p.val) [prot.initial]

theorem transcript_eq_iff_forall_send_at
    (prot : BlackboardProtocol P L R)
    (candidate reference : EdgePartition P L R) :
    prot.transcript candidate = prot.transcript reference ↔
      ∀ p : Fin P,
        prot.send p (candidate.block p) (prot.historyBefore reference p) =
          prot.send p (reference.block p) (prot.historyBefore reference p) := by
  rw [transcript_eq_iff_followsReference,
    followsReference_iff_forall_position]
  constructor
  · intro h p
    let n : Fin (List.finRange P).length :=
      Fin.cast (List.length_finRange P).symm p
    have hn : (List.finRange P).get n = p := by
      apply Fin.ext
      rw [List.get_finRange]
      rfl
    simpa [historyBefore, n, hn] using h n
  · intro h n
    let p : Fin P := Fin.cast (List.length_finRange P) n
    have hp : (List.finRange P).get n = p := by
      apply Fin.ext
      rw [List.get_finRange]
      rfl
    simpa [historyBefore, p, hp] using h p

theorem conditionalMessageScheme_expectedBelong_le_forty
    [Fintype L] [Fintype R]
    (prot : BlackboardProtocol P L R) {s q : ℕ}
    [DecidableEq prot.Message]
    (hprot : prot.UsesCommunication s) (p : Fin P)
    (history : List prot.Message)
    (hq0 : 0 < q) (hqlt : q < Fintype.card (Edge L R))
    (hqhalf : 2 * q ≤ Fintype.card (Edge L R))
    (hcorr : (Fintype.card (Edge L R) : ℝ) *
        FiniteDist.binaryEntropy
          ((q : ℝ) / Fintype.card (Edge L R)) -
        Real.log (Nat.choose (Fintype.card (Edge L R)) q) ≤
          (s : ℝ) * Real.log 2) :
    Compression.expectedBelong
        (Compression.fixedCardDist (E := Edge L R) q hqlt.le)
        (prot.conditionalMessageScheme p history)
        ((q : ℝ) / Fintype.card (Edge L R)) ≤
      40 * (s : ℝ) * Real.log 2 /
        ((q : ℝ) / Fintype.card (Edge L R)) := by
  letI : Nonempty prot.Message := ⟨prot.initial⟩
  exact Compression.fixedCard_expectedBelong_le_forty_of_correlation
    (prot.conditionalMessageScheme p history) s q hq0 hqlt hqhalf
    hprot.messageCard_le hcorr

end BlackboardProtocol

theorem fintype_card_subtype_eq_filter_card
    {A : Type*} [Fintype A] (predicate : A → Prop)
    [DecidablePred predicate] :
    Fintype.card {a : A // predicate a} =
      ((Finset.univ : Finset A).filter predicate).card := by
  classical
  let equiv : {a : A // predicate a} ≃
      {a : A // a ∈ (Finset.univ : Finset A).filter predicate} :=
    { toFun := fun a ↦ ⟨a.1, by simpa using a.2⟩
      invFun := fun a ↦ ⟨a.1, by simpa using a.2⟩
      left_inv := by intro a; apply Subtype.ext; rfl
      right_inv := by intro a; apply Subtype.ext; rfl }
  calc
    Fintype.card {a : A // predicate a} =
        Fintype.card
          {a : A // a ∈ (Finset.univ : Finset A).filter predicate} :=
      Fintype.card_congr equiv
    _ = ((Finset.univ : Finset A).filter predicate).card :=
      Fintype.card_coe _

namespace FiniteDist

variable {Omega Xi E : Type*}
  [Fintype Omega] [Fintype Xi] [Fintype E] [DecidableEq E]

theorem expect_inter_card_le
    (Q : FiniteDist Xi) (B : Finset E) (relevant : Xi → Finset E)
    (lambda : ℝ)
    (hprob : ∀ e ∈ B, Q.prob (fun xi ↦ e ∈ relevant xi) ≤ lambda) :
    Q.expect (fun xi ↦ ((B ∩ relevant xi).card : ℝ)) ≤
      lambda * B.card := by
  classical
  have hcard (xi : Xi) :
      ((B ∩ relevant xi).card : ℝ) =
        ∑ e in B, if e ∈ relevant xi then 1 else 0 := by
    have hset : B ∩ relevant xi = B.filter (fun e ↦ e ∈ relevant xi) := by
      ext e
      simp [and_comm]
    rw [hset]
    norm_cast
    exact Finset.card_filter (fun e ↦ e ∈ relevant xi) B
  calc
    Q.expect (fun xi ↦ ((B ∩ relevant xi).card : ℝ)) =
        Q.expect (fun xi ↦ ∑ e in B,
          if e ∈ relevant xi then 1 else 0) := by
      apply congrArg (Q.expect)
      funext xi
      exact hcard xi
    _ = ∑ e in B, Q.prob (fun xi ↦ e ∈ relevant xi) := by
      unfold FiniteDist.expect FiniteDist.prob
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite]
      simp
    _ ≤ ∑ _e in B, lambda :=
      Finset.sum_le_sum fun e he ↦ hprob e he
    _ = lambda * B.card := by simp [mul_comm]

theorem expect_expect_inter_card_le
    (Pdist : FiniteDist Omega) (Q : FiniteDist Xi)
    (recoverable : Omega → Finset E)
    (relevant : Omega → Xi → Finset E) (lambda : ℝ)
    (hprob : ∀ omega e, e ∈ recoverable omega →
      Q.prob (fun xi ↦ e ∈ relevant omega xi) ≤ lambda) :
    Pdist.expect (fun omega ↦
        Q.expect (fun xi ↦
          ((recoverable omega ∩ relevant omega xi).card : ℝ))) ≤
      lambda * Pdist.expect (fun omega ↦
        ((recoverable omega).card : ℝ)) := by
  calc
    Pdist.expect (fun omega ↦
        Q.expect (fun xi ↦
          ((recoverable omega ∩ relevant omega xi).card : ℝ))) ≤
        Pdist.expect (fun omega ↦
          lambda * ((recoverable omega).card : ℝ)) := by
      apply Pdist.expect_mono
      intro omega
      exact Q.expect_inter_card_le (recoverable omega) (relevant omega) lambda
        (fun e he ↦ hprob omega e he)
    _ = lambda * Pdist.expect (fun omega ↦
        ((recoverable omega).card : ℝ)) :=
      Pdist.expect_smul lambda _

end FiniteDist

namespace FixedCardPosterior

variable {E M : Type*} [Fintype E] [DecidableEq E]
  [Fintype M] [DecidableEq M]

def extendSummary (q : ℕ) (summary : FixedCard E q → M) (default : M) :
    Compression.Scheme E M :=
  fun D ↦ if hD : D.card = q then summary ⟨D, hD⟩ else default

@[simp]
theorem extendSummary_apply (q : ℕ) (summary : FixedCard E q → M)
    (default : M) (D : FixedCard E q) :
    extendSummary q summary default D.1 = summary D := by
  simp only [extendSummary, dif_pos D.2]

def deletedFiber (q : ℕ) (summary : FixedCard E q → M)
    (msg : M) (e : E) : Finset (FixedCard E q) :=
  (UniformPosterior.fiber summary msg).filter fun D ↦ e ∈ D.1

theorem deletedFiber_eq_filter (q : ℕ) (summary : FixedCard E q → M)
    (msg : M) (e : E) :
    deletedFiber q summary msg e =
      Finset.univ.filter (fun D ↦ summary D = msg ∧ e ∈ D.1) := by
  classical
  ext D
  simp [deletedFiber, UniformPosterior.fiber]

theorem fiber_image_val (q : ℕ) (summary : FixedCard E q → M)
    (default msg : M) :
    (UniformPosterior.fiber summary msg).image Subtype.val =
      Compression.fixedCardFiber q (extendSummary q summary default) msg := by
  classical
  ext D
  constructor
  · intro hD
    rw [Finset.mem_image] at hD
    obtain ⟨X, hX, rfl⟩ := hD
    rw [Compression.fixedCardFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, X.2, by
      simpa [UniformPosterior.fiber] using hX⟩
  · intro hD
    rw [Compression.fixedCardFiber, Finset.mem_filter] at hD
    rcases hD with ⟨_univ, hcard, hsummary⟩
    rw [Finset.mem_image]
    refine ⟨⟨D, hcard⟩, ?_, rfl⟩
    change extendSummary q summary default (⟨D, hcard⟩ : FixedCard E q).1 = msg
      at hsummary
    rw [extendSummary_apply] at hsummary
    simpa [UniformPosterior.fiber] using hsummary

theorem fiber_card_eq (q : ℕ) (summary : FixedCard E q → M)
    (default msg : M) :
    (UniformPosterior.fiber summary msg).card =
      (Compression.fixedCardFiber q (extendSummary q summary default) msg).card := by
  rw [← fiber_image_val q summary default msg]
  exact (Finset.card_image_iff.mpr (by
    intro A _hA B _hB hab
    exact Subtype.ext hab)).symm

theorem deletedFiber_image_val (q : ℕ) (summary : FixedCard E q → M)
    (default msg : M) (e : E) :
    (deletedFiber q summary msg e).image Subtype.val =
      Compression.fixedCardDeletedFiber q
        (extendSummary q summary default) msg e := by
  classical
  ext D
  constructor
  · intro hD
    rw [Finset.mem_image] at hD
    obtain ⟨X, hX, rfl⟩ := hD
    rw [Compression.fixedCardDeletedFiber, Finset.mem_filter]
    exact ⟨by
      rw [← fiber_image_val q summary default msg]
      exact Finset.mem_image.2 ⟨X, (Finset.mem_filter.1 hX).1, rfl⟩,
      (Finset.mem_filter.1 hX).2⟩
  · intro hD
    rw [Compression.fixedCardDeletedFiber, Finset.mem_filter] at hD
    rcases hD with ⟨hFiber, heD⟩
    rw [← fiber_image_val q summary default msg, Finset.mem_image] at hFiber
    obtain ⟨X, hX, rfl⟩ := hFiber
    rw [Finset.mem_image]
    exact ⟨X, Finset.mem_filter.2 ⟨hX, heD⟩, rfl⟩

theorem deletedFiber_card_eq (q : ℕ) (summary : FixedCard E q → M)
    (default msg : M) (e : E) :
    (deletedFiber q summary msg e).card =
      (Compression.fixedCardDeletedFiber q
        (extendSummary q summary default) msg e).card := by
  rw [← deletedFiber_image_val q summary default msg e]
  exact (Finset.card_image_iff.mpr (by
    intro A _hA B _hB hab
    exact Subtype.ext hab)).symm

theorem belongingEdges_subset_belongSet
    (q : ℕ) (hq : q ≤ Fintype.card E)
    (summary : FixedCard E q → M) (default : M)
    {eta : ℚ} {delta : ℝ} (heta : (eta : ℝ) = delta / 2)
    (D : FixedCard E q) :
    UniformPosterior.belongingEdges eta summary
        (fun X e ↦ e ∉ X.1) (summary D) ⊆
      Compression.belongSet
        (Compression.fixedCardDist (E := E) q hq)
        (extendSummary q summary default) delta (summary D) := by
  classical
  intro e he
  rw [UniformPosterior.mem_belongingEdges_iff] at he
  rw [Compression.mem_belongSet_fixedCard_iff]
  let F := UniformPosterior.fiber summary (summary D)
  let Z := deletedFiber q summary (summary D) e
  let K := UniformPosterior.presentFiber summary (fun X e ↦ e ∉ X.1)
    (summary D) e
  have hDF : D ∈ F := by simp [F, UniformPosterior.fiber]
  have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨D, hDF⟩
  have hpartition : Z.card + K.card = F.card := by
    have hZ : Z = F.filter (fun X : FixedCard E q ↦ e ∈ X.1) := by
      rfl
    have hK : K = F.filter (fun X : FixedCard E q ↦ e ∉ X.1) := by
      ext X
      simp [K, F, UniformPosterior.presentFiber, UniformPosterior.fiber]
    rw [hZ, hK]
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (fun X : FixedCard E q ↦ e ∈ X.1)
  have hdeletedQ : (Z.card : ℚ) ≤ eta * F.card := by
    change (1 - eta) * (F.card : ℚ) ≤ (K.card : ℚ) at he
    have hpartitionQ : (Z.card : ℚ) + K.card = F.card := by
      exact_mod_cast hpartition
    linarith
  have hdeletedR : (Z.card : ℝ) ≤ (delta / 2) * F.card := by
    have hcast : (Z.card : ℝ) ≤ (eta : ℝ) * F.card := by
      exact_mod_cast hdeletedQ
    simpa [heta] using hcast
  constructor
  · rw [← fiber_card_eq q summary default (summary D)]
    exact hFpos
  · rw [← deletedFiber_card_eq q summary default (summary D) e,
      ← fiber_card_eq q summary default (summary D)]
    exact (div_le_iff (by exact_mod_cast hFpos : (0 : ℝ) < F.card)).2
      hdeletedR

theorem expectedBelong_eq_fixedCard_uniform
    (q : ℕ) (hq : q ≤ Fintype.card E)
    (summary : FixedCard E q → M) (default : M) (delta : ℝ) :
    Compression.expectedBelong
        (Compression.fixedCardDist (E := E) q hq)
        (extendSummary q summary default) delta =
      (FixedCard.uniform q hq).expect (fun D ↦
        ((Compression.belongSet
          (Compression.fixedCardDist (E := E) q hq)
          (extendSummary q summary default) delta (summary D)).card : ℝ)) := by
  classical
  letI : Nonempty (FixedCard E q) := FixedCard.nonempty q hq
  rw [Compression.expectedBelong_eq_input_expect]
  change
    (Compression.fixedCardDist (E := E) q hq).expect (fun D ↦
        ((Compression.belongSet
          (Compression.fixedCardDist (E := E) q hq)
          (extendSummary q summary default) delta
          (extendSummary q summary default D)).card : ℝ)) =
      (FiniteDist.uniform (FixedCard E q)).expect (fun D ↦
        ((Compression.belongSet
          (Compression.fixedCardDist (E := E) q hq)
          (extendSummary q summary default) delta (summary D)).card : ℝ))
  rw [FiniteDist.uniform_expect]
  unfold FiniteDist.expect
  simp_rw [Compression.fixedCardDist_mass]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  let f : Finset E → ℝ := fun D ↦
    (1 / (Nat.choose (Fintype.card E) q : ℝ)) *
      ((Compression.belongSet
        (Compression.fixedCardDist (E := E) q hq)
        (extendSummary q summary default) delta
        (extendSummary q summary default D)).card : ℝ)
  have hsum :
      (∑ D in (Finset.univ : Finset (Finset E)).filter
          (fun D ↦ D.card = q), f D) =
        ∑ D : FixedCard E q, f D.1 := by
    exact Finset.sum_subtype
      (p := fun D : Finset E ↦ D.card = q)
      ((Finset.univ : Finset (Finset E)).filter fun D ↦ D.card = q)
      (fun _ ↦ by simp) f
  rw [hsum]
  simp_rw [f, extendSummary_apply]
  rw [FixedCard.card, ← Finset.mul_sum]
  ring

theorem uniform_expected_belongSet_le_forty
    (q bits : ℕ) (summary : FixedCard E q → M) (default : M)
    (delta : ℝ) (hq0 : 0 < q) (hqlt : q < Fintype.card E)
    (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ bits)
    (hbudget : Real.log (Fintype.card E + 1) ≤
      (bits : ℝ) * Real.log 2)
    (hdelta : delta = (q : ℝ) / Fintype.card E) :
    (FixedCard.uniform q hqlt.le).expect (fun D ↦
        ((Compression.belongSet
          (Compression.fixedCardDist (E := E) q hqlt.le)
          (extendSummary q summary default) delta (summary D)).card : ℝ)) ≤
      40 * (bits : ℝ) * Real.log 2 / delta := by
  rw [← expectedBelong_eq_fixedCard_uniform q hqlt.le summary default delta]
  letI : Nonempty M := ⟨default⟩
  rw [hdelta]
  exact Compression.fixedCard_expectedBelong_le_forty
    (extendSummary q summary default) bits q hq0 hqlt hqhalf hcard hbudget

theorem uniform_expected_belongSet_le_bits_log_succ
    (q bits : ℕ) (summary : FixedCard E q → M) (default : M)
    (delta : ℝ) (hq0 : 0 < q) (hqlt : q < Fintype.card E)
    (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ bits)
    (hdelta : delta = (q : ℝ) / Fintype.card E) :
    (FixedCard.uniform q hqlt.le).expect (fun D ↦
        ((Compression.belongSet
          (Compression.fixedCardDist (E := E) q hqlt.le)
          (extendSummary q summary default) delta (summary D)).card : ℝ)) ≤
      (20 / delta) *
        ((bits : ℝ) * Real.log 2 + Real.log (Fintype.card E + 1)) := by
  rw [← expectedBelong_eq_fixedCard_uniform q hqlt.le summary default delta]
  letI : Nonempty M := ⟨default⟩
  rw [hdelta]
  exact Compression.fixedCard_expectedBelong_le_bits_log_succ
    (extendSummary q summary default) bits q hq0 hqlt hqhalf hcard

theorem uniform_expected_posteriorBelong_le_forty_of_correlation
    (q s : ℕ) (summary : FixedCard E q → M) (default : M)
    {eta : ℚ} {delta : ℝ} (heta : (eta : ℝ) = delta / 2)
    (hq0 : 0 < q) (hqlt : q < Fintype.card E)
    (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s)
    (hcorr : (Fintype.card E : ℝ) *
        FiniteDist.binaryEntropy ((q : ℝ) / Fintype.card E) -
          Real.log (Nat.choose (Fintype.card E) q) ≤
            (s : ℝ) * Real.log 2)
    (hdelta : delta = (q : ℝ) / Fintype.card E) :
    (FixedCard.uniform q hqlt.le).expect (fun D ↦
        ((UniformPosterior.belongingEdges eta summary
          (fun X e ↦ e ∉ X.1) (summary D)).card : ℝ)) ≤
      40 * (s : ℝ) * Real.log 2 / delta := by
  let P := Compression.fixedCardDist (E := E) q hqlt.le
  let Phi := extendSummary q summary default
  have hpoint (D : FixedCard E q) :
      ((UniformPosterior.belongingEdges eta summary
        (fun X e ↦ e ∉ X.1) (summary D)).card : ℝ) ≤
        ((Compression.belongSet P Phi delta (summary D)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (belongingEdges_subset_belongSet q hqlt.le summary default heta D)
  calc
    (FixedCard.uniform q hqlt.le).expect (fun D ↦
        ((UniformPosterior.belongingEdges eta summary
          (fun X e ↦ e ∉ X.1) (summary D)).card : ℝ)) ≤
        (FixedCard.uniform q hqlt.le).expect (fun D ↦
          ((Compression.belongSet P Phi delta (summary D)).card : ℝ)) :=
      (FixedCard.uniform q hqlt.le).expect_mono hpoint
    _ = Compression.expectedBelong P Phi delta := by
      symm
      exact expectedBelong_eq_fixedCard_uniform q hqlt.le summary default delta
    _ ≤ 40 * (s : ℝ) * Real.log 2 /
        ((q : ℝ) / Fintype.card E) := by
      letI : Nonempty M := ⟨default⟩
      rw [hdelta]
      exact Compression.fixedCard_expectedBelong_le_forty_of_correlation
        Phi s q hq0 hqlt hqhalf hcard hcorr
    _ = 40 * (s : ℝ) * Real.log 2 / delta := by rw [hdelta]

theorem uniform_expected_posteriorBelong_le_forty
    (q s : ℕ) (summary : FixedCard E q → M) (default : M)
    {eta : ℚ} {delta : ℝ} (heta : (eta : ℝ) = delta / 2)
    (hq0 : 0 < q) (hqlt : q < Fintype.card E)
    (hqhalf : 2 * q ≤ Fintype.card E)
    (hcard : Fintype.card M ≤ 2 ^ s)
    (hbudget : Real.log (Fintype.card E + 1) ≤
      (s : ℝ) * Real.log 2)
    (hdelta : delta = (q : ℝ) / Fintype.card E) :
    (FixedCard.uniform q hqlt.le).expect (fun D ↦
        ((UniformPosterior.belongingEdges eta summary
          (fun X e ↦ e ∉ X.1) (summary D)).card : ℝ)) ≤
      40 * (s : ℝ) * Real.log 2 / delta := by
  apply uniform_expected_posteriorBelong_le_forty_of_correlation
    q s summary default heta hq0 hqlt hqhalf hcard
    ((Compression.fixedCard_totalCorrelation_le_log_succ
      (Fintype.card E) q hq0 hqlt).trans hbudget) hdelta

end FixedCardPosterior

namespace UniformPosterior

variable {Omega S E : Type*}
  [Fintype Omega] [Fintype S] [Fintype E]
  [DecidableEq Omega] [DecidableEq S] [DecidableEq E]

theorem filter_card_mul_succ_le_sum_card
    (X : Omega → Finset E) (q : ℕ) :
    (((Finset.univ.filter fun omega ↦ q < (X omega).card).card : ℕ) : ℚ) *
        (q + 1) ≤
      ∑ omega : Omega, ((X omega).card : ℚ) := by
  have hnat :
      (Finset.univ.filter fun omega ↦ q < (X omega).card).card * (q + 1) ≤
        ∑ omega : Omega, (X omega).card := by
    calc
      (Finset.univ.filter fun omega ↦ q < (X omega).card).card * (q + 1) =
          ∑ omega in Finset.univ.filter (fun omega ↦ q < (X omega).card),
            (q + 1) := by simp
      _ ≤ ∑ omega in Finset.univ.filter (fun omega ↦ q < (X omega).card),
          (X omega).card := by
        apply Finset.sum_le_sum
        intro omega homega
        exact Nat.succ_le_iff.mpr (Finset.mem_filter.1 homega).2
      _ ≤ ∑ omega : Omega, (X omega).card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro omega _hmem _hnot
        exact Nat.zero_le _
  exact_mod_cast hnat

theorem manyBelongingRelevant_card_le_of_sum
    {eta beta : ℚ} (summary : Omega → S) (present : Omega → E → Prop)
    (relevant : S → Finset E) (q : ℕ)
    (hsum :
      (∑ omega : Omega,
        ((belongingEdges eta summary present (summary omega) ∩
          relevant (summary omega)).card : ℚ)) ≤
        beta * (q + 1) * Fintype.card Omega) :
    ((manyBelongingRelevantSamples eta summary present relevant q).card : ℚ) ≤
      beta * Fintype.card Omega := by
  let X : Omega → Finset E := fun omega ↦
    belongingEdges eta summary present (summary omega) ∩
      relevant (summary omega)
  have hmarkov := filter_card_mul_succ_le_sum_card X q
  have hevent :
      Finset.univ.filter (fun omega ↦ q < (X omega).card) =
        manyBelongingRelevantSamples eta summary present relevant q := by
    ext omega
    simp [X, manyBelongingRelevantSamples, HasManyBelongingRelevant]
  rw [hevent] at hmarkov
  have hpos : (0 : ℚ) < q + 1 := by positivity
  nlinarith

noncomputable def absentFiber (summary : Omega → S)
    (present : Omega → E → Prop) (s : S) (e : E) : Finset Omega := by
  classical
  exact (fiber summary s).filter fun omega ↦ ¬ present omega e

theorem presentFiber_card_add_absentFiber_card
    (summary : Omega → S) (present : Omega → E → Prop)
    (s : S) (e : E) :
    (presentFiber summary present s e).card +
        (absentFiber summary present s e).card =
      (fiber summary s).card := by
  classical
  unfold presentFiber absentFiber
  simpa using (Finset.filter_card_add_filter_neg_card_eq_card
    (s := fiber summary s) (fun omega ↦ present omega e))

theorem absentFiber_card_le_of_belongs
    {eta : ℚ} (summary : Omega → S) (present : Omega → E → Prop)
    (s : S) (e : E) (hbelongs : Belongs eta summary present s e) :
    ((absentFiber summary present s e).card : ℚ) ≤
      eta * (fiber summary s).card := by
  have hpartition := presentFiber_card_add_absentFiber_card
    summary present s e
  unfold Belongs at hbelongs
  have hpartitionQ :
      ((presentFiber summary present s e).card : ℚ) +
          (absentFiber summary present s e).card =
        (fiber summary s).card := by
    exact_mod_cast hpartition
  linarith

end UniformPosterior

namespace FixedCardPosterior

variable {Omega Summary LocalEdge GlobalEdge Message : Type*}
  [Fintype Omega] [Fintype Summary] [Fintype LocalEdge]
  [Fintype GlobalEdge] [Fintype Message]
  [DecidableEq Omega] [DecidableEq Summary] [DecidableEq LocalEdge]
  [DecidableEq GlobalEdge] [DecidableEq Message]

theorem mem_belongSet_of_global_belongs_of_card_factorization
    (q : ℕ) (hq : q ≤ Fintype.card LocalEdge)
    (scheme : Compression.Scheme LocalEdge Message) (msg : Message)
    (edge : LocalEdge) (globalEdge : GlobalEdge) (delta : ℝ)
    (summary : Omega → Summary) (present : Omega → GlobalEdge → Prop)
    (s : Summary) {eta : ℚ}
    (heta : (eta : ℝ) ≤ delta / 2)
    (hglobalPos : 0 < (UniformPosterior.fiber summary s).card)
    (hlocalPos : 0 < (Compression.fixedCardFiber q scheme msg).card)
    (hfactor :
      (UniformPosterior.absentFiber summary present s globalEdge).card *
          (Compression.fixedCardFiber q scheme msg).card =
        (UniformPosterior.fiber summary s).card *
          (Compression.fixedCardDeletedFiber q scheme msg edge).card)
    (hbelongs : UniformPosterior.Belongs eta summary present s globalEdge) :
    edge ∈ Compression.belongSet
      (Compression.fixedCardDist q hq) scheme delta msg := by
  rw [Compression.mem_belongSet_fixedCard_iff]
  refine ⟨hlocalPos, ?_⟩
  have habsentQ := UniformPosterior.absentFiber_card_le_of_belongs
    summary present s globalEdge hbelongs
  have habsentR :
      ((UniformPosterior.absentFiber summary present s globalEdge).card : ℝ) ≤
        (eta : ℝ) * (UniformPosterior.fiber summary s).card := by
    exact_mod_cast habsentQ
  have hfactorR :
      ((UniformPosterior.absentFiber summary present s globalEdge).card : ℝ) *
          (Compression.fixedCardFiber q scheme msg).card =
        (UniformPosterior.fiber summary s).card *
          (Compression.fixedCardDeletedFiber q scheme msg edge).card := by
    exact_mod_cast hfactor
  have hglobalPosR :
      (0 : ℝ) < (UniformPosterior.fiber summary s).card := by
    exact_mod_cast hglobalPos
  have hlocalPosR :
      (0 : ℝ) < (Compression.fixedCardFiber q scheme msg).card := by
    exact_mod_cast hlocalPos
  rw [div_le_iff hlocalPosR]
  have habsentMul := mul_le_mul_of_nonneg_right habsentR hlocalPosR.le
  have hglobalMul :
      ((UniformPosterior.fiber summary s).card : ℝ) *
          ((Compression.fixedCardDeletedFiber q scheme msg edge).card : ℝ) ≤
        ((UniformPosterior.fiber summary s).card : ℝ) *
          ((eta : ℝ) *
            ((Compression.fixedCardFiber q scheme msg).card : ℝ)) := by
    calc
      ((UniformPosterior.fiber summary s).card : ℝ) *
          ((Compression.fixedCardDeletedFiber q scheme msg edge).card : ℝ) =
        ((UniformPosterior.absentFiber summary present s globalEdge).card : ℝ) *
          ((Compression.fixedCardFiber q scheme msg).card : ℝ) :=
            hfactorR.symm
      _ ≤ ((eta : ℝ) *
          ((UniformPosterior.fiber summary s).card : ℝ)) *
          ((Compression.fixedCardFiber q scheme msg).card : ℝ) := habsentMul
      _ = ((UniformPosterior.fiber summary s).card : ℝ) *
          ((eta : ℝ) *
            ((Compression.fixedCardFiber q scheme msg).card : ℝ)) := by
        ring
  have hdeletedEta :
      ((Compression.fixedCardDeletedFiber q scheme msg edge).card : ℝ) ≤
        (eta : ℝ) * (Compression.fixedCardFiber q scheme msg).card :=
    (mul_le_mul_left hglobalPosR).mp hglobalMul
  exact hdeletedEta.trans
    (mul_le_mul_of_nonneg_right heta hlocalPosR.le)

end FixedCardPosterior

namespace FinitePartitionDistribution

variable {P : ℕ} {L R : Type*}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def graphPresent (D : FinitePartitionDistribution P L R)
    (x : D.Sample) (e : Edge L R) : Prop :=
  e ∈ (D.input x).graph.edges

structure ProtocolPosteriorModel
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (prot : BlackboardProtocol P L R) where
  Summary : Type
  summaryFintype : Fintype Summary
  summaryDecidableEq : DecidableEq Summary
  summary : D.Sample → Summary
  output : Summary → Finset (Edge L R)
  relevant : Summary → Finset (Edge L R)
  output_eq : ∀ x, output (summary x) = prot.result (D.input x)
  relevant_on_output : ∀ x,
    output (summary x) ⊆ (D.input x).graph.edges →
    output (summary x) ∩ relevant (summary x) =
      prot.result (D.input x) ∩ (cert x).special

namespace ProtocolPosteriorModel

variable {D : FinitePartitionDistribution P L R}
  {cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph}
  {prot : BlackboardProtocol P L R}

theorem feasible_of_succeeds (W : ProtocolPosteriorModel D cert prot)
    (x : D.Sample) (hsuc : prot.SucceedsOn rho (D.input x)) :
    UniformPosterior.Feasible W.summary D.graphPresent W.output x := by
  intro e he
  rw [W.output_eq x] at he
  exact hsuc.1.1 he

theorem hasManyRelevant_iff_discoversManySpecial
    (W : ProtocolPosteriorModel D cert prot) (q : ℕ) (x : D.Sample)
    (hpresent : W.output (W.summary x) ⊆ (D.input x).graph.edges) :
    UniformPosterior.HasManyRelevant W.summary W.output W.relevant q x ↔
      D.DiscoversManySpecial cert q prot x := by
  unfold UniformPosterior.HasManyRelevant DiscoversManySpecial
  rw [W.relevant_on_output x hpresent]

end ProtocolPosteriorModel

end FinitePartitionDistribution

namespace HardDistribution

open SimpleExpansion AugmentedExpansion

variable {L0 R0 : Type} {r t : ℕ}
  [Fintype L0] [Fintype R0] [DecidableEq L0] [DecidableEq R0]

theorem part_eq_of_agreeBefore
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (p : Fin B.P) {J K : IndexTuple B t}
    (hJK : AgreeBefore p J K) :
    part B H J p = part B H K p := by
  classical
  ext z
  simp only [mem_part_iff]
  constructor
  · rintro ⟨W, hWJ, hzW⟩
    exact ⟨W, fun i hi ↦ (hWJ i hi).trans (hJK i hi), hzW⟩
  · rintro ⟨W, hWK, hzW⟩
    exact ⟨W, fun i hi ↦ (hWK i hi).trans (hJK i hi).symm, hzW⟩

abbrev PrefixIndexTuple (B : SimpleProperBlueprint) (t : ℕ) (p : Fin B.P) :=
  {i : Fin B.P // i < p} → Fin t

def combinePrefixSuffix (B : SimpleProperBlueprint) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p) :
    IndexTuple B t := fun i ↦
  if hi : i < p then pref ⟨i, hi⟩ else suffix ⟨i, le_of_not_gt hi⟩

@[simp]
theorem combinePrefixSuffix_prefix (B : SimpleProperBlueprint) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (i : Fin B.P) (hi : i < p) :
    combinePrefixSuffix B p pref suffix i = pref ⟨i, hi⟩ := by
  simp [combinePrefixSuffix, hi]

@[simp]
theorem combinePrefixSuffix_suffix (B : SimpleProperBlueprint) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (i : Fin B.P) (hi : p ≤ i) :
    combinePrefixSuffix B p pref suffix i = suffix ⟨i, hi⟩ := by
  simp [combinePrefixSuffix, not_lt_of_ge hi]

def indexTupleEquivPrefixSuffix (B : SimpleProperBlueprint) (p : Fin B.P) :
    IndexTuple B t ≃ PrefixIndexTuple B t p × SuffixIndexTuple B t p where
  toFun J := (fun i ↦ J i.1, fun i ↦ J i.1)
  invFun data := combinePrefixSuffix B p data.1 data.2
  left_inv J := by
    funext i
    by_cases hi : i < p
    · simp [combinePrefixSuffix, hi]
    · simp [combinePrefixSuffix, hi]
  right_inv data := by
    apply Prod.ext
    · funext i
      simp [combinePrefixSuffix, i.2]
    · funext i
      simp [combinePrefixSuffix, not_lt_of_ge i.2]

theorem agreeBefore_combinePrefixSuffix
    (B : SimpleProperBlueprint) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix suffix' : SuffixIndexTuple B t p) :
    AgreeBefore p (combinePrefixSuffix B p pref suffix)
      (combinePrefixSuffix B p pref suffix') := by
  intro i hi
  simp [combinePrefixSuffix, hi]

def playerEdgeEquivOfPartEq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P)
    (hpart : part B H J p = part B H K p) :
    {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} ≃
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H K p} where
  toFun z := ⟨z.1, by simpa [hpart] using z.2⟩
  invFun z := ⟨z.1, by simpa [hpart] using z.2⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

@[simp]
theorem playerEdgeEquivOfPartEq_val
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P)
    (hpart : part B H J p = part B H K p)
    (z : {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    (playerEdgeEquivOfPartEq B H J K p hpart z).1 = z.1 := rfl

noncomputable def playerDeletionEquivOfPartEq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hpart : part B H J p = part B H K p) :
    PlayerDeletion B H J p qDelete ≃ PlayerDeletion B H K p qDelete :=
  let edgeEquiv := playerEdgeEquivOfPartEq B H J K p hpart
  { toFun := fun deleted ↦ ⟨edgeEquiv.finsetCongr deleted.1, by
      simpa using deleted.2⟩
    invFun := fun deleted ↦ ⟨edgeEquiv.symm.finsetCongr deleted.1, by
      simpa using deleted.2⟩
    left_inv := by
      intro deleted
      apply Subtype.ext
      exact edgeEquiv.finsetCongr.left_inv deleted.1
    right_inv := by
      intro deleted
      apply Subtype.ext
      exact edgeEquiv.finsetCongr.right_inv deleted.1 }

theorem deletionEdges_playerDeletionEquivOfPartEq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hpart : part B H J p = part B H K p)
    (deleted : PlayerDeletion B H J p qDelete) :
    deletionEdges (playerDeletionEquivOfPartEq B H J K p qDelete hpart deleted) =
      deletionEdges deleted := by
  classical
  let edgeEquiv := playerEdgeEquivOfPartEq B H J K p hpart
  change (edgeEquiv.finsetCongr deleted.1).image Subtype.val =
    deleted.1.image Subtype.val
  rw [edgeEquiv.finsetCongr_apply]
  ext z
  simp only [Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨edgeEquiv v, ⟨v, hv, rfl⟩, ?_⟩
    rfl

def prefixRepresentative
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (p : Fin B.P) (pref : PrefixIndexTuple B t p) : IndexTuple B t :=
  combinePrefixSuffix B p pref (fun _ ↦ ⟨0, H.t_pos⟩)

theorem completeWithSuffix_prefixRepresentative
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (p : Fin B.P) (pref : PrefixIndexTuple B t p)
    (suffix : SuffixIndexTuple B t p) :
    completeWithSuffix p (prefixRepresentative B H p pref) suffix =
      combinePrefixSuffix B p pref suffix := by
  funext i
  by_cases hip : p ≤ i
  · simp [completeWithSuffix, combinePrefixSuffix, hip,
      not_lt_of_ge hip]
  · have hip' : i < p := lt_of_not_ge hip
    simp [completeWithSuffix, prefixRepresentative, combinePrefixSuffix,
      hip, hip']

theorem part_eq_prefixRepresentative_of_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (p : Fin B.P) (pref : PrefixIndexTuple B t p)
    (suffix : SuffixIndexTuple B t p) (i : Fin B.P) (hip : i ≤ p) :
    part B H (combinePrefixSuffix B p pref suffix) i =
      part B H (prefixRepresentative B H p pref) i := by
  apply part_eq_of_agreeBefore B H i
  intro j hji
  have hjp : j < p := lt_of_lt_of_le hji hip
  simp [prefixRepresentative, combinePrefixSuffix, hjp]

noncomputable def deletionProfileEquivPrefixRepresentative
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p) :
    DeletionProfile B H deletions (combinePrefixSuffix B p pref suffix) ≃
      DeletionProfile B H deletions (prefixRepresentative B H p pref) :=
  Equiv.piCongrRight fun i ↦
    if hip : i ≤ p then
      playerDeletionEquivOfPartEq B H _ _ i (deletions i)
        (part_eq_prefixRepresentative_of_le B H p pref suffix i hip)
    else
      Fintype.equivOfCardEq (by
        rw [playerDeletion_card, playerDeletion_card])

theorem deletionProfileEquivPrefixRepresentative_apply_of_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (profile : DeletionProfile B H deletions
      (combinePrefixSuffix B p pref suffix))
    (i : Fin B.P) (hip : i ≤ p) :
    (deletionProfileEquivPrefixRepresentative B H deletions p pref suffix
      profile) i =
      playerDeletionEquivOfPartEq B H
        (combinePrefixSuffix B p pref suffix)
        (prefixRepresentative B H p pref) i (deletions i)
        (part_eq_prefixRepresentative_of_le B H p pref suffix i hip)
        (profile i) := by
  change
    (if _h : i ≤ p then
      playerDeletionEquivOfPartEq B H _ _ i (deletions i)
        (part_eq_prefixRepresentative_of_le B H p pref suffix i _h)
      else Fintype.equivOfCardEq (by
        rw [playerDeletion_card, playerDeletion_card])) (profile i) = _
  rw [dif_pos hip]

theorem deletionEdges_profileEquivPrefixRepresentative_of_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (profile : DeletionProfile B H deletions
      (combinePrefixSuffix B p pref suffix))
    (i : Fin B.P) (hip : i ≤ p) :
    deletionEdges
        ((deletionProfileEquivPrefixRepresentative B H deletions p pref suffix
          profile) i) =
      deletionEdges (profile i) := by
  change deletionEdges
      ((if _h : i ≤ p then
          playerDeletionEquivOfPartEq B H _ _ i (deletions i)
            (part_eq_prefixRepresentative_of_le B H p pref suffix i _h)
        else Fintype.equivOfCardEq (by
          rw [playerDeletion_card, playerDeletion_card])) (profile i)) =
    deletionEdges (profile i)
  rw [dif_pos hip]
  exact deletionEdges_playerDeletionEquivOfPartEq B H _ _ i (deletions i)
    (part_eq_prefixRepresentative_of_le B H p pref suffix i hip) (profile i)

abbrev ThroughPlayers (B : SimpleProperBlueprint) (p : Fin B.P) :=
  {i : Fin B.P // i ≤ p}

abbrev LaterPlayers (B : SimpleProperBlueprint) (p : Fin B.P) :=
  {i : Fin B.P // p < i}

abbrev ThroughDeletionProfile
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) :=
  (i : ThroughPlayers B p) →
    PlayerDeletion B H (prefixRepresentative B H p pref) i.1 (deletions i.1)

abbrev LaterDeletionProfile
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) :=
  (i : LaterPlayers B p) →
    PlayerDeletion B H (prefixRepresentative B H p pref) i.1 (deletions i.1)

def deletionProfileEquivThroughLater
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) :
    DeletionProfile B H deletions (prefixRepresentative B H p pref) ≃
      ThroughDeletionProfile B H deletions p pref ×
        LaterDeletionProfile B H deletions p pref where
  toFun profile := (fun i ↦ profile i.1, fun i ↦ profile i.1)
  invFun data i := if hip : i ≤ p then data.1 ⟨i, hip⟩
    else data.2 ⟨i, lt_of_not_ge hip⟩
  left_inv profile := by
    funext i
    by_cases hip : i ≤ p <;> simp [hip]
  right_inv data := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext i
      simp [not_le_of_gt i.2]

def representativeDeletionProfile
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    DeletionProfile B H deletions (prefixRepresentative B H p pref) :=
  (deletionProfileEquivThroughLater B H deletions p pref).symm
    (through, later)

noncomputable def reindexedSample
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    Sample B H deletions :=
  ⟨combinePrefixSuffix B p pref suffix,
    (deletionProfileEquivPrefixRepresentative B H deletions p pref suffix).symm
      (representativeDeletionProfile B H deletions p pref through later)⟩

@[simp]
theorem representativeDeletionProfile_through
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref)
    (i : ThroughPlayers B p) :
    representativeDeletionProfile B H deletions p pref through later i.1 =
      through i := by
  simp [representativeDeletionProfile, deletionProfileEquivThroughLater, i.2]

@[simp]
theorem representativeDeletionProfile_later
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (pref : PrefixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref)
    (i : LaterPlayers B p) :
    representativeDeletionProfile B H deletions p pref through later i.1 =
      later i := by
  simp [representativeDeletionProfile, deletionProfileEquivThroughLater,
    not_le_of_gt i.2]

theorem sum_sample_eq_prefix_suffix_through_later
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (f : Sample B H deletions → ℝ) :
    (∑ sample : Sample B H deletions, f sample) =
      ∑ pref : PrefixIndexTuple B t p,
        ∑ suffix : SuffixIndexTuple B t p,
          ∑ through : ThroughDeletionProfile B H deletions p pref,
            ∑ later : LaterDeletionProfile B H deletions p pref,
              f ⟨combinePrefixSuffix B p pref suffix,
                (deletionProfileEquivPrefixRepresentative B H deletions p pref
                  suffix).symm
                  ((deletionProfileEquivThroughLater B H deletions p pref).symm
                    (through, later))⟩ := by
  classical
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  calc
    (∑ J : IndexTuple B t,
        ∑ profile : DeletionProfile B H deletions J, f ⟨J, profile⟩) =
        ∑ data : PrefixIndexTuple B t p × SuffixIndexTuple B t p,
          ∑ profile : DeletionProfile B H deletions
              (combinePrefixSuffix B p data.1 data.2),
            f ⟨combinePrefixSuffix B p data.1 data.2, profile⟩ := by
      symm
      apply Fintype.sum_equiv (indexTupleEquivPrefixSuffix B p).symm
      intro data
      rfl
    _ = ∑ pref : PrefixIndexTuple B t p,
        ∑ suffix : SuffixIndexTuple B t p,
          ∑ profile : DeletionProfile B H deletions
              (combinePrefixSuffix B p pref suffix),
            f ⟨combinePrefixSuffix B p pref suffix, profile⟩ := by
      rw [Fintype.sum_prod_type]
    _ = ∑ pref : PrefixIndexTuple B t p,
        ∑ suffix : SuffixIndexTuple B t p,
          ∑ profile : DeletionProfile B H deletions
              (prefixRepresentative B H p pref),
            f ⟨combinePrefixSuffix B p pref suffix,
              (deletionProfileEquivPrefixRepresentative B H deletions p pref
                suffix).symm profile⟩ := by
      apply Finset.sum_congr rfl
      intro pref _hpref
      apply Finset.sum_congr rfl
      intro suffix _hsuffix
      symm
      apply Fintype.sum_equiv
        (deletionProfileEquivPrefixRepresentative B H deletions p pref
          suffix).symm
      intro profile
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pref _hpref
      apply Finset.sum_congr rfl
      intro suffix _hsuffix
      calc
        (∑ profile : DeletionProfile B H deletions
            (prefixRepresentative B H p pref),
          f ⟨combinePrefixSuffix B p pref suffix,
            (deletionProfileEquivPrefixRepresentative B H deletions p pref
              suffix).symm profile⟩) =
            ∑ data : ThroughDeletionProfile B H deletions p pref ×
                LaterDeletionProfile B H deletions p pref,
              f ⟨combinePrefixSuffix B p pref suffix,
                (deletionProfileEquivPrefixRepresentative B H deletions p pref
                  suffix).symm
                  ((deletionProfileEquivThroughLater B H deletions p pref).symm
                    data)⟩ := by
          symm
          apply Fintype.sum_equiv
            (deletionProfileEquivThroughLater B H deletions p pref).symm
          intro data
          rfl
        _ = _ := Fintype.sum_prod_type

noncomputable def protocolSummary
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (sample : Sample B H deletions) :
    IndexTuple B t × prot.TranscriptCode :=
  (sample.1, prot.transcriptCode (edgePartition sample))

theorem mem_deletionEdges_iff
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (deleted : PlayerDeletion B H J p qDelete)
    (z : BaseEdge (L := L0) (R := R0) B) (hz : z ∈ part B H J p) :
    z ∈ deletionEdges deleted ↔
      (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
        w ∈ part B H J p}) ∈ deleted.1 := by
  classical
  constructor
  · intro h
    rw [deletionEdges, Finset.mem_image] at h
    obtain ⟨w, hw, hwz⟩ := h
    have : w = ⟨z, hz⟩ := Subtype.ext hwz
    simpa [this] using hw
  · intro h
    rw [deletionEdges, Finset.mem_image]
    exact ⟨⟨z, hz⟩, h, rfl⟩

theorem mem_keptEdges_iff_not_mem_playerDeletion
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (sample : Sample B H deletions)
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H sample.1 p) :
    z ∈ keptEdges sample ↔
      (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
        w ∈ part B H sample.1 p}) ∉ (sample.2 p).1 := by
  classical
  constructor
  · intro hkept
    rw [keptEdges, Finset.mem_biUnion] at hkept
    obtain ⟨i, _hi, hi⟩ := hkept
    have hzi : z ∈ part B H sample.1 i := (Finset.mem_sdiff.1 hi).1
    have hip : i = p := by
      by_contra hne
      exact Finset.disjoint_left.1 (parts_disjoint B H sample.1 hne)
        hzi hz
    subst i
    have hzNotDeleted : z ∉ deletionEdges (sample.2 p) :=
      (Finset.mem_sdiff.1 hi).2
    exact fun h ↦ hzNotDeleted
      ((mem_deletionEdges_iff B H sample.1 p (deletions p)
        (sample.2 p) z hz).2 h)
  · intro hnot
    rw [keptEdges, Finset.mem_biUnion]
    refine ⟨p, Finset.mem_univ _, Finset.mem_sdiff.2 ⟨hz, ?_⟩⟩
    intro hdeleted
    exact hnot ((mem_deletionEdges_iff B H sample.1 p (deletions p)
      (sample.2 p) z hz).1 hdeleted)

theorem graphPresent_liftEdge_iff_not_mem_playerDeletion
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (sample : Sample B H deletions) (p : Fin B.P)
    (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H sample.1 p) :
    (finitePartitionDistribution B H deletions hdeletions).graphPresent
        sample (liftEdge z) ↔
      (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
        w ∈ part B H sample.1 p}) ∉ (sample.2 p).1 := by
  classical
  change liftEdge z ∈ (edgePartition sample).graph.edges ↔ _
  rw [edgePartition_graph]
  change liftEdge z ∈ liftEdges (keptEdges sample) ∪ externalInput sample ↔ _
  have hzGraph : z ∈ (SimpleExpansion.graph B H sample.1).edges := by
    rw [SimpleExpansion.mem_graph_iff]
    exact ⟨p, hz⟩
  have hzNotExternal : liftEdge z ∉ externalInput sample := by
    exact fun hext ↦ Finset.disjoint_left.1
      (liftEdges_disjoint_externalMatching (canonicalMatching B H sample.1)
        (SimpleExpansion.graph B H sample.1).edges)
      (mem_liftEdges_iff.2 hzGraph) hext
  rw [Finset.mem_union, or_iff_left hzNotExternal, mem_liftEdges_iff,
    mem_keptEdges_iff_not_mem_playerDeletion B H deletions sample p z hz]

noncomputable def playerReferenceHistory
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (p : Fin B.P) : List prot.Message :=
  prot.historyBefore (edgePartition (⟨J, reference⟩ : Sample B H deletions))
    p.castSucc

theorem playerReferenceHistory_eq_of_agreeBefore
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (p : Fin B.P)
    (J K : IndexTuple B t)
    (profileJ : DeletionProfile B H deletions J)
    (profileK : DeletionProfile B H deletions K)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (hJK : AgreeBefore p J K)
    (hdeleted : ∀ i, i < p →
      deletionEdges (profileJ i) = deletionEdges (profileK i)) :
    playerReferenceHistory B H deletions J profileJ prot p =
      playerReferenceHistory B H deletions K profileK prot p := by
  unfold playerReferenceHistory BlackboardProtocol.historyBefore
  apply prot.playFrom_congr_blocks
  intro q hq
  have hqp : q.val < p.val :=
    BlackboardProtocol.val_lt_of_mem_take_finRange q hq
  let i : Fin B.P := ⟨q.val, lt_trans hqp p.isLt⟩
  have hqi : q = i.castSucc := by
    apply Fin.ext
    rfl
  calc
    (edgePartition ⟨J, profileJ⟩).block q =
        (edgePartition ⟨J, profileJ⟩).block i.castSucc :=
      congrArg (edgePartition ⟨J, profileJ⟩).block hqi
    _ = (edgePartition ⟨K, profileK⟩).block i.castSucc := by
      simp only [edgePartition, block_castSucc]
      apply congrArg liftEdges
      unfold keptPart
      have hip : i < p := hqp
      have hpart : part B H J i = part B H K i := by
        apply part_eq_of_agreeBefore B H i
        intro j hji
        exact hJK j (lt_trans hji hip)
      rw [hpart, hdeleted i hip]
    _ = (edgePartition ⟨K, profileK⟩).block q :=
      congrArg (edgePartition ⟨K, profileK⟩).block hqi.symm

noncomputable def playerMessageScheme
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (history : List prot.Message) :
    Compression.Scheme
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}
      prot.Message :=
  fun deleted ↦ prot.send p.castSucc
    (liftEdges (part B H J p \ deleted.image Subtype.val)) history

noncomputable def playerMessageSummary
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (history : List prot.Message) :
    PlayerDeletion B H J p qDelete → prot.Message :=
  fun deleted ↦ playerMessageScheme B H J p prot history deleted.1

theorem playerMessageSummary_eq_send
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (history : List prot.Message)
    (deleted : PlayerDeletion B H J p qDelete) :
    playerMessageSummary B H J p qDelete prot history deleted =
      prot.send p.castSucc
        (liftEdges (part B H J p \ deletionEdges deleted)) history := by
  rfl

theorem playerMessageSummary_playerDeletionEquivOfPartEq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hpart : part B H J p = part B H K p)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (historyJ historyK : List prot.Message) (hhistory : historyJ = historyK)
    (deleted : PlayerDeletion B H J p qDelete) :
    playerMessageSummary B H K p qDelete prot historyK
        (playerDeletionEquivOfPartEq B H J K p qDelete hpart deleted) =
      playerMessageSummary B H J p qDelete prot historyJ deleted := by
  rw [playerMessageSummary_eq_send, playerMessageSummary_eq_send,
    ← hhistory, ← hpart,
    deletionEdges_playerDeletionEquivOfPartEq B H J K p qDelete hpart deleted]

theorem mem_playerDeletionEquivOfPartEq_iff
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hpart : part B H J p = part B H K p)
    (deleted : PlayerDeletion B H J p qDelete)
    (z : {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    playerEdgeEquivOfPartEq B H J K p hpart z ∈
        (playerDeletionEquivOfPartEq B H J K p qDelete hpart deleted).1 ↔
      z ∈ deleted.1 := by
  classical
  simp [playerDeletionEquivOfPartEq]

theorem fixedJ_transcript_eq_iff_playerMessages
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (candidate reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)) :
    prot.transcript (edgePartition
        (⟨J, candidate⟩ : Sample B H deletions)) =
      prot.transcript (edgePartition
        (⟨J, reference⟩ : Sample B H deletions)) ↔
      ∀ p : Fin B.P,
        playerMessageSummary B H J p (deletions p) prot
            (playerReferenceHistory B H deletions J reference prot p)
            (candidate p) =
          playerMessageSummary B H J p (deletions p) prot
            (playerReferenceHistory B H deletions J reference prot p)
            (reference p) := by
  rw [prot.transcript_eq_iff_forall_send_at]
  constructor
  · intro hall p
    simpa [playerReferenceHistory, playerMessageSummary_eq_send, keptPart,
      edgePartition]
      using hall p.castSucc
  · intro hall i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨p, rfl⟩ | rfl
    · simpa [playerReferenceHistory, playerMessageSummary_eq_send, keptPart,
        edgePartition]
        using hall p
    · simp [BlackboardProtocol.historyBefore, edgePartition, externalInput]

abbrev FixedJTranscriptFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)) :=
  {candidate : DeletionProfile B H deletions J //
    prot.transcript (edgePartition
        (⟨J, candidate⟩ : Sample B H deletions)) =
      prot.transcript (edgePartition
        (⟨J, reference⟩ : Sample B H deletions))}

abbrev PlayerMessageFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (p : Fin B.P) :=
  {deleted : PlayerDeletion B H J p (deletions p) //
    playerMessageSummary B H J p (deletions p) prot
        (playerReferenceHistory B H deletions J reference prot p) deleted =
      playerMessageSummary B H J p (deletions p) prot
        (playerReferenceHistory B H deletions J reference prot p)
        (reference p)}

noncomputable def replacePlayerDeletion
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (profile : DeletionProfile B H deletions J) (p : Fin B.P)
    (deleted : PlayerDeletion B H J p (deletions p)) :
    DeletionProfile B H deletions J := fun i ↦
  if h : i = p then by subst i; exact deleted else profile i

@[simp]
theorem replacePlayerDeletion_same
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (profile : DeletionProfile B H deletions J) (p : Fin B.P)
    (deleted : PlayerDeletion B H J p (deletions p)) :
    replacePlayerDeletion B H deletions J profile p deleted p = deleted := by
  simp [replacePlayerDeletion]

@[simp]
theorem replacePlayerDeletion_of_ne
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (profile : DeletionProfile B H deletions J) (p i : Fin B.P)
    (deleted : PlayerDeletion B H J p (deletions p)) (hip : i ≠ p) :
    replacePlayerDeletion B H deletions J profile p deleted i = profile i := by
  simp [replacePlayerDeletion, hip]

theorem replacePlayerDeletion_self
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (profile : DeletionProfile B H deletions J) (p : Fin B.P) :
    replacePlayerDeletion B H deletions J profile p (profile p) = profile := by
  funext i
  by_cases hip : i = p
  · subst i
    simp
  · simp [hip]

theorem replacePlayerDeletion_twice
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (profile : DeletionProfile B H deletions J) (p : Fin B.P)
    (first second : PlayerDeletion B H J p (deletions p)) :
    replacePlayerDeletion B H deletions J
        (replacePlayerDeletion B H deletions J profile p first) p second =
      replacePlayerDeletion B H deletions J profile p second := by
  funext i
  by_cases hip : i = p
  · subst i
    simp
  · simp [hip]

def fixedJTranscriptFiberEquivPlayerMessageFibers
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)) :
    FixedJTranscriptFiber B H deletions J reference prot ≃
      ((p : Fin B.P) →
        PlayerMessageFiber B H deletions J reference prot p) where
  toFun candidate p := ⟨candidate.1 p,
    (fixedJ_transcript_eq_iff_playerMessages
      B H deletions J candidate.1 reference prot).1 candidate.2 p⟩
  invFun fibers := ⟨(fun p ↦ (fibers p).1),
    (fixedJ_transcript_eq_iff_playerMessages
      B H deletions J (fun p ↦ (fibers p).1) reference prot).2
        (fun p ↦ (fibers p).2)⟩
  left_inv candidate := by
    apply Subtype.ext
    rfl
  right_inv fibers := by
    funext p
    apply Subtype.ext
    rfl

abbrev FixedJDeletedTranscriptFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H J p) :=
  {candidate : FixedJTranscriptFiber B H deletions J reference prot //
    (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
      w ∈ part B H J p}) ∈ (candidate.1 p).1}

abbrev PlayerDeletedMessageFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H J p) :=
  {deleted : PlayerMessageFiber B H deletions J reference prot p //
    (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
      w ∈ part B H J p}) ∈ deleted.1.1}

def playerMessageFiberOfFixedJ
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (candidate : FixedJTranscriptFiber B H deletions J reference prot)
    (p : Fin B.P) :
    PlayerMessageFiber B H deletions J reference prot p :=
  ⟨candidate.1 p,
    (fixedJ_transcript_eq_iff_playerMessages
      B H deletions J candidate.1 reference prot).1 candidate.2 p⟩

noncomputable def replaceFixedJTranscriptCoordinate
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (candidate : FixedJTranscriptFiber B H deletions J reference prot)
    (p : Fin B.P)
    (newDeleted : PlayerMessageFiber B H deletions J reference prot p) :
    FixedJTranscriptFiber B H deletions J reference prot :=
  ⟨replacePlayerDeletion B H deletions J candidate.1 p newDeleted.1,
    (fixedJ_transcript_eq_iff_playerMessages B H deletions J
      (replacePlayerDeletion B H deletions J candidate.1 p newDeleted.1)
      reference prot).2 (by
        intro i
        by_cases hip : i = p
        · subst i
          simpa using newDeleted.2
        · simpa [replacePlayerDeletion_of_ne, hip] using
            (fixedJ_transcript_eq_iff_playerMessages B H deletions J
              candidate.1 reference prot).1 candidate.2 i)⟩

noncomputable def fixedJFiberSwapEquiv
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H J p) :
    (FixedJTranscriptFiber B H deletions J reference prot ×
      PlayerDeletedMessageFiber B H deletions J reference prot p z hz) ≃
    (FixedJDeletedTranscriptFiber B H deletions J reference prot p z hz ×
      PlayerMessageFiber B H deletions J reference prot p) where
  toFun pair :=
    let replaced := replaceFixedJTranscriptCoordinate B H deletions J reference
      prot pair.1 p pair.2.1
    (⟨replaced, by simpa [replaced, replaceFixedJTranscriptCoordinate]
      using pair.2.2⟩,
      playerMessageFiberOfFixedJ B H deletions J reference prot pair.1 p)
  invFun pair :=
    let replaced := replaceFixedJTranscriptCoordinate B H deletions J reference
      prot pair.1.1 p pair.2
    (replaced,
      ⟨playerMessageFiberOfFixedJ B H deletions J reference prot pair.1.1 p,
        pair.1.2⟩)
  left_inv pair := by
    rcases pair with ⟨candidate, newDeleted⟩
    apply Prod.ext
    · apply Subtype.ext
      change replacePlayerDeletion B H deletions J
          (replacePlayerDeletion B H deletions J candidate.1 p newDeleted.1.1)
          p (candidate.1 p) = candidate.1
      rw [replacePlayerDeletion_twice, replacePlayerDeletion_self]
    · apply Subtype.ext
      apply Subtype.ext
      change replacePlayerDeletion B H deletions J candidate.1 p
          newDeleted.1.1 p = newDeleted.1.1
      simp
  right_inv pair := by
    rcases pair with ⟨deletedCandidate, oldDeleted⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change replacePlayerDeletion B H deletions J
          (replacePlayerDeletion B H deletions J deletedCandidate.1.1 p
            oldDeleted.1) p (deletedCandidate.1.1 p) = deletedCandidate.1.1
      rw [replacePlayerDeletion_twice, replacePlayerDeletion_self]
    · apply Subtype.ext
      change replacePlayerDeletion B H deletions J deletedCandidate.1.1 p
          oldDeleted.1 p = oldDeleted.1
      simp

abbrev GlobalProtocolFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions) :=
  {sample : Sample B H deletions // sample ∈
    UniformPosterior.fiber (protocolSummary B H deletions prot)
      (protocolSummary B H deletions prot reference)}

abbrev GlobalProtocolAbsentFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions)
    (z : BaseEdge (L := L0) (R := R0) B) :=
  {sample : Sample B H deletions // sample ∈
    UniformPosterior.absentFiber (protocolSummary B H deletions prot)
      (finitePartitionDistribution B H deletions hdeletions).graphPresent
      (protocolSummary B H deletions prot reference) (liftEdge z)}

noncomputable def globalProtocolFiberEquivFixedJ
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions) :
    GlobalProtocolFiber B H deletions prot reference ≃
      FixedJTranscriptFiber B H deletions reference.1 reference.2 prot where
  toFun sample := by
    rcases sample with ⟨⟨J, profile⟩, hsample⟩
    have hsummary :
        protocolSummary B H deletions prot ⟨J, profile⟩ =
          protocolSummary B H deletions prot reference := by
      simpa [UniformPosterior.fiber] using hsample
    have hJ : J = reference.1 := congrArg Prod.fst hsummary
    subst J
    refine ⟨profile, ?_⟩
    apply (prot.transcriptCode_eq_iff _ _).1
    exact congrArg Prod.snd hsummary
  invFun candidate := by
    refine ⟨⟨reference.1, candidate.1⟩, ?_⟩
    simp only [UniformPosterior.fiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    apply Prod.ext
    · rfl
    · exact (prot.transcriptCode_eq_iff _ _).2 candidate.2
  left_inv sample := by
    rcases sample with ⟨⟨J, profile⟩, hsample⟩
    apply Subtype.ext
    have hsummary :
        protocolSummary B H deletions prot ⟨J, profile⟩ =
          protocolSummary B H deletions prot reference := by
      simpa [UniformPosterior.fiber] using hsample
    have hJ : J = reference.1 := congrArg Prod.fst hsummary
    subst J
    rfl
  right_inv candidate := by
    apply Subtype.ext
    rfl

noncomputable def globalProtocolAbsentFiberEquivFixedJDeleted
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions)
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H reference.1 p) :
    GlobalProtocolAbsentFiber B H deletions hdeletions prot reference z ≃
      FixedJDeletedTranscriptFiber B H deletions reference.1 reference.2 prot
        p z hz where
  toFun sample := by
    rcases sample with ⟨⟨J, profile⟩, hsample⟩
    have hdata :
        protocolSummary B H deletions prot ⟨J, profile⟩ =
            protocolSummary B H deletions prot reference ∧
          ¬ (finitePartitionDistribution B H deletions hdeletions).graphPresent
            ⟨J, profile⟩ (liftEdge z) := by
      simpa [UniformPosterior.absentFiber, UniformPosterior.fiber] using hsample
    have hJ : J = reference.1 := congrArg Prod.fst hdata.1
    subst J
    let fixed : FixedJTranscriptFiber B H deletions reference.1 reference.2
        prot := ⟨profile, (prot.transcriptCode_eq_iff _ _).1
          (congrArg Prod.snd hdata.1)⟩
    refine ⟨fixed, ?_⟩
    by_contra hnot
    apply hdata.2
    exact (graphPresent_liftEdge_iff_not_mem_playerDeletion B H deletions
      hdeletions ⟨reference.1, profile⟩ p z hz).2 hnot
  invFun candidate := by
    refine ⟨⟨reference.1, candidate.1.1⟩, ?_⟩
    simp only [UniformPosterior.absentFiber, UniformPosterior.fiber,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · apply Prod.ext
      · rfl
      · exact (prot.transcriptCode_eq_iff _ _).2 candidate.1.2
    · intro hpresent
      exact ((graphPresent_liftEdge_iff_not_mem_playerDeletion B H deletions
        hdeletions ⟨reference.1, candidate.1.1⟩ p z hz).1 hpresent)
        candidate.2
  left_inv sample := by
    rcases sample with ⟨⟨J, profile⟩, hsample⟩
    apply Subtype.ext
    have hdata :
        protocolSummary B H deletions prot ⟨J, profile⟩ =
            protocolSummary B H deletions prot reference ∧
          ¬ (finitePartitionDistribution B H deletions hdeletions).graphPresent
            ⟨J, profile⟩ (liftEdge z) := by
      simpa [UniformPosterior.absentFiber, UniformPosterior.fiber] using hsample
    have hJ : J = reference.1 := congrArg Prod.fst hdata.1
    subst J
    rfl
  right_inv candidate := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem globalProtocolFiber_card_eq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions) :
    Fintype.card (GlobalProtocolFiber B H deletions prot reference) =
      (UniformPosterior.fiber (protocolSummary B H deletions prot)
        (protocolSummary B H deletions prot reference)).card := by
  simpa [GlobalProtocolFiber] using Fintype.card_coe
    (UniformPosterior.fiber (protocolSummary B H deletions prot)
      (protocolSummary B H deletions prot reference))

theorem globalProtocolAbsentFiber_card_eq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions)
    (z : BaseEdge (L := L0) (R := R0) B) :
    Fintype.card
        (GlobalProtocolAbsentFiber B H deletions hdeletions prot reference z) =
      (UniformPosterior.absentFiber (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot reference) (liftEdge z)).card := by
  simpa [GlobalProtocolAbsentFiber] using Fintype.card_coe
    (UniformPosterior.absentFiber (protocolSummary B H deletions prot)
      (finitePartitionDistribution B H deletions hdeletions).graphPresent
      (protocolSummary B H deletions prot reference) (liftEdge z))

set_option maxHeartbeats 1000000

theorem playerMessageFiber_card_eq_compressionFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P) :
    Fintype.card (PlayerMessageFiber B H deletions J reference prot p) =
      (Compression.fixedCardFiber (deletions p)
        (FixedCardPosterior.extendSummary (deletions p)
          (playerMessageSummary B H J p (deletions p) prot
            (playerReferenceHistory B H deletions J reference prot p))
          prot.initial)
        (playerMessageSummary B H J p (deletions p) prot
          (playerReferenceHistory B H deletions J reference prot p)
          (reference p))).card := by
  let summary := playerMessageSummary B H J p (deletions p) prot
    (playerReferenceHistory B H deletions J reference prot p)
  let msg := summary (reference p)
  change Fintype.card
      {deleted : PlayerDeletion B H J p (deletions p) //
        summary deleted = msg} =
    (Compression.fixedCardFiber (deletions p)
      (FixedCardPosterior.extendSummary (deletions p) summary prot.initial)
      msg).card
  rw [fintype_card_subtype_eq_filter_card]
  exact FixedCardPosterior.fiber_card_eq
    (deletions p) summary prot.initial msg

theorem playerDeletedMessageFiber_card_eq_compressionDeletedFiber
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ) (J : IndexTuple B t)
    (reference : DeletionProfile B H deletions J)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P)
    (z : BaseEdge (L := L0) (R := R0) B) (hz : z ∈ part B H J p) :
    Fintype.card
        (PlayerDeletedMessageFiber B H deletions J reference prot p z hz) =
      (Compression.fixedCardDeletedFiber (deletions p)
        (FixedCardPosterior.extendSummary (deletions p)
          (playerMessageSummary B H J p (deletions p) prot
            (playerReferenceHistory B H deletions J reference prot p))
          prot.initial)
        (playerMessageSummary B H J p (deletions p) prot
          (playerReferenceHistory B H deletions J reference prot p)
          (reference p)) ⟨z, hz⟩).card := by
  let summary := playerMessageSummary B H J p (deletions p) prot
    (playerReferenceHistory B H deletions J reference prot p)
  let msg := summary (reference p)
  let edge : {w : BaseEdge (L := L0) (R := R0) B // w ∈ part B H J p} :=
    ⟨z, hz⟩
  change Fintype.card
      {deleted : {D : PlayerDeletion B H J p (deletions p) //
        summary D = msg} // edge ∈ deleted.1.1} =
    (Compression.fixedCardDeletedFiber (deletions p)
      (FixedCardPosterior.extendSummary (deletions p) summary prot.initial)
      msg edge).card
  let equiv : {deleted : {D : PlayerDeletion B H J p (deletions p) //
        summary D = msg} // edge ∈ deleted.1.1} ≃
      {deleted : PlayerDeletion B H J p (deletions p) //
        summary deleted = msg ∧ edge ∈ deleted.1} :=
    { toFun := fun deleted ↦
        ⟨deleted.1.1, deleted.1.2, deleted.2⟩
      invFun := fun deleted ↦
        ⟨⟨deleted.1, deleted.2.1⟩, deleted.2.2⟩
      left_inv := by intro deleted; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro deleted; apply Subtype.ext; rfl }
  calc
    Fintype.card
        (PlayerDeletedMessageFiber B H deletions J reference prot p z hz) =
        Fintype.card
          {deleted : PlayerDeletion B H J p (deletions p) //
            summary deleted = msg ∧ edge ∈ deleted.1} :=
      Fintype.card_congr equiv
    _ = ((Finset.univ : Finset (PlayerDeletion B H J p (deletions p))).filter
        (fun deleted ↦ summary deleted = msg ∧ edge ∈ deleted.1)).card :=
      fintype_card_subtype_eq_filter_card _
    _ = (FixedCardPosterior.deletedFiber
        (deletions p) summary msg edge).card := by
      exact congrArg Finset.card
        (FixedCardPosterior.deletedFiber_eq_filter
          (deletions p) summary msg edge).symm
    _ = (Compression.fixedCardDeletedFiber (deletions p)
        (FixedCardPosterior.extendSummary (deletions p) summary prot.initial)
        msg edge).card :=
      FixedCardPosterior.deletedFiber_card_eq (deletions p) summary
        prot.initial msg edge

theorem protocolPosterior_card_factorization
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions)
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H reference.1 p) :
    (UniformPosterior.absentFiber (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot reference) (liftEdge z)).card *
      (Compression.fixedCardFiber (deletions p)
        (FixedCardPosterior.extendSummary (deletions p)
          (playerMessageSummary B H reference.1 p (deletions p) prot
            (playerReferenceHistory B H deletions reference.1 reference.2 prot p))
          prot.initial)
        (playerMessageSummary B H reference.1 p (deletions p) prot
          (playerReferenceHistory B H deletions reference.1 reference.2 prot p)
          (reference.2 p))).card =
    (UniformPosterior.fiber (protocolSummary B H deletions prot)
        (protocolSummary B H deletions prot reference)).card *
      (Compression.fixedCardDeletedFiber (deletions p)
        (FixedCardPosterior.extendSummary (deletions p)
          (playerMessageSummary B H reference.1 p (deletions p) prot
            (playerReferenceHistory B H deletions reference.1 reference.2 prot p))
          prot.initial)
        (playerMessageSummary B H reference.1 p (deletions p) prot
          (playerReferenceHistory B H deletions reference.1 reference.2 prot p)
          (reference.2 p)) ⟨z, hz⟩).card := by
  have hswap := Fintype.card_congr
    (fixedJFiberSwapEquiv B H deletions reference.1 reference.2 prot p z hz)
  rw [Fintype.card_prod, Fintype.card_prod] at hswap
  have hswap' :
      Fintype.card
          (FixedJTranscriptFiber B H deletions reference.1 reference.2 prot) *
        Fintype.card
          (PlayerDeletedMessageFiber B H deletions reference.1 reference.2
            prot p z hz) =
      Fintype.card
          (FixedJDeletedTranscriptFiber B H deletions reference.1 reference.2
            prot p z hz) *
        Fintype.card
          (PlayerMessageFiber B H deletions reference.1 reference.2 prot p) := by
    exact hswap
  have hglobal :
      (UniformPosterior.fiber (protocolSummary B H deletions prot)
          (protocolSummary B H deletions prot reference)).card =
        Fintype.card
          (FixedJTranscriptFiber B H deletions reference.1 reference.2 prot) := by
    calc
      _ = Fintype.card (GlobalProtocolFiber B H deletions prot reference) :=
        (globalProtocolFiber_card_eq B H deletions prot reference).symm
      _ = _ := Fintype.card_congr
        (globalProtocolFiberEquivFixedJ B H deletions prot reference)
  have habsent :
      (UniformPosterior.absentFiber (protocolSummary B H deletions prot)
          (finitePartitionDistribution B H deletions hdeletions).graphPresent
          (protocolSummary B H deletions prot reference) (liftEdge z)).card =
        Fintype.card
          (FixedJDeletedTranscriptFiber B H deletions reference.1 reference.2
            prot p z hz) := by
    calc
      _ = Fintype.card (GlobalProtocolAbsentFiber B H deletions hdeletions
          prot reference z) :=
        (globalProtocolAbsentFiber_card_eq B H deletions hdeletions prot
          reference z).symm
      _ = _ := Fintype.card_congr
        (globalProtocolAbsentFiberEquivFixedJDeleted B H deletions hdeletions
          prot reference p z hz)
  have hlocal := playerMessageFiber_card_eq_compressionFiber
    B H deletions reference.1 reference.2 prot p
  have hdeleted := playerDeletedMessageFiber_card_eq_compressionDeletedFiber
    B H deletions reference.1 reference.2 prot p z hz
  calc
    _ = Fintype.card
          (FixedJDeletedTranscriptFiber B H deletions reference.1 reference.2
            prot p z hz) *
        Fintype.card
          (PlayerMessageFiber B H deletions reference.1 reference.2 prot p) := by
      rw [habsent, hlocal]
    _ = Fintype.card
          (FixedJTranscriptFiber B H deletions reference.1 reference.2 prot) *
        Fintype.card
          (PlayerDeletedMessageFiber B H deletions reference.1 reference.2
            prot p z hz) := hswap'.symm
    _ = _ := by rw [hglobal, hdeleted]

theorem globalBelongs_imp_mem_playerBelongSet
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (reference : Sample B H deletions)
    (p : Fin B.P) (z : BaseEdge (L := L0) (R := R0) B)
    (hz : z ∈ part B H reference.1 p) {eta : ℚ} (delta : ℝ)
    (heta : (eta : ℝ) ≤ delta / 2)
    (hbelongs : UniformPosterior.Belongs eta
      (protocolSummary B H deletions prot)
      (finitePartitionDistribution B H deletions hdeletions).graphPresent
      (protocolSummary B H deletions prot reference) (liftEdge z)) :
    (⟨z, hz⟩ : {w : BaseEdge (L := L0) (R := R0) B //
      w ∈ part B H reference.1 p}) ∈
      Compression.belongSet
        (Compression.fixedCardDist (deletions p) (by
          simpa using hdeletions reference.1 p))
        (FixedCardPosterior.extendSummary (deletions p)
          (playerMessageSummary B H reference.1 p (deletions p) prot
            (playerReferenceHistory B H deletions reference.1 reference.2 prot p))
          prot.initial)
        delta
        (playerMessageSummary B H reference.1 p (deletions p) prot
          (playerReferenceHistory B H deletions reference.1 reference.2 prot p)
          (reference.2 p)) := by
  let summary := playerMessageSummary B H reference.1 p (deletions p) prot
    (playerReferenceHistory B H deletions reference.1 reference.2 prot p)
  let scheme := FixedCardPosterior.extendSummary (deletions p) summary prot.initial
  let msg := summary (reference.2 p)
  let edge : {w : BaseEdge (L := L0) (R := R0) B //
      w ∈ part B H reference.1 p} := ⟨z, hz⟩
  have hq : deletions p ≤ Fintype.card
      {w : BaseEdge (L := L0) (R := R0) B //
        w ∈ part B H reference.1 p} := by
    simpa using hdeletions reference.1 p
  have hglobalPos : 0 <
      (UniformPosterior.fiber (protocolSummary B H deletions prot)
        (protocolSummary B H deletions prot reference)).card := by
    apply Finset.card_pos.mpr
    refine ⟨reference, ?_⟩
    simp [UniformPosterior.fiber]
  have hlocalPos : 0 <
      (Compression.fixedCardFiber (deletions p) scheme msg).card := by
    apply Finset.card_pos.mpr
    refine ⟨(reference.2 p).1, ?_⟩
    rw [Compression.fixedCardFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (reference.2 p).2, ?_⟩
    simp [scheme, summary, msg, FixedCardPosterior.extendSummary_apply]
  change edge ∈ Compression.belongSet
    (Compression.fixedCardDist (deletions p) hq) scheme delta msg
  apply FixedCardPosterior.mem_belongSet_of_global_belongs_of_card_factorization
    (deletions p) hq scheme msg edge (liftEdge z) delta
    (protocolSummary B H deletions prot)
    (finitePartitionDistribution B H deletions hdeletions).graphPresent
    (protocolSummary B H deletions prot reference) heta hglobalPos hlocalPos
  · simpa [scheme, summary, msg, edge] using
      protocolPosterior_card_factorization B H deletions hdeletions prot
        reference p z hz
  · exact hbelongs

set_option maxHeartbeats 200000

noncomputable def playerBelongSet
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hq : qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (history : List prot.Message) (delta : ℝ)
    (deleted : PlayerDeletion B H J p qDelete) :
    Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} :=
  Compression.belongSet (Compression.fixedCardDist qDelete hq)
    (FixedCardPosterior.extendSummary qDelete
      (playerMessageSummary B H J p qDelete prot history) prot.initial)
    delta (playerMessageSummary B H J p qDelete prot history deleted)

set_option maxHeartbeats 1000000

theorem mem_playerBelongSet_playerEdgeEquivOfPartEq_iff
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J K : IndexTuple B t) (p : Fin B.P) (qDelete : ℕ)
    (hpart : part B H J p = part B H K p)
    (hqJ : qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hqK : qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H K p})
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (historyJ historyK : List prot.Message) (hhistory : historyJ = historyK)
    (delta : ℝ) (deleted : PlayerDeletion B H J p qDelete)
    (z : {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    z ∈ playerBelongSet B H J p qDelete hqJ prot historyJ delta deleted ↔
      playerEdgeEquivOfPartEq B H J K p hpart z ∈
        playerBelongSet B H K p qDelete hqK prot historyK delta
          (playerDeletionEquivOfPartEq B H J K p qDelete hpart deleted) := by
  classical
  let edgeEquiv := playerEdgeEquivOfPartEq B H J K p hpart
  let deletionEquiv :=
    playerDeletionEquivOfPartEq B H J K p qDelete hpart
  let summaryJ := playerMessageSummary B H J p qDelete prot historyJ
  let summaryK := playerMessageSummary B H K p qDelete prot historyK
  let msgJ := summaryJ deleted
  let msgK := summaryK (deletionEquiv deleted)
  let schemeJ := FixedCardPosterior.extendSummary qDelete summaryJ prot.initial
  let schemeK := FixedCardPosterior.extendSummary qDelete summaryK prot.initial
  have hsummary (D : PlayerDeletion B H J p qDelete) :
      summaryK (deletionEquiv D) = summaryJ D := by
    exact playerMessageSummary_playerDeletionEquivOfPartEq
      B H J K p qDelete hpart prot historyJ historyK hhistory D
  let fiberEquiv : {D : PlayerDeletion B H J p qDelete //
        summaryJ D = msgJ} ≃
      {D : PlayerDeletion B H K p qDelete // summaryK D = msgK} :=
    { toFun := fun D ↦ ⟨deletionEquiv D.1, by
          change summaryK (deletionEquiv D.1) =
            summaryK (deletionEquiv deleted)
          rw [hsummary D.1, hsummary deleted]
          exact D.2⟩
      invFun := fun D ↦ ⟨deletionEquiv.symm D.1, by
          have hD := hsummary (deletionEquiv.symm D.1)
          have href := hsummary deleted
          rw [deletionEquiv.apply_symm_apply] at hD
          change summaryJ (deletionEquiv.symm D.1) = summaryJ deleted
          rw [← hD, ← href]
          exact D.2⟩
      left_inv := by intro D; apply Subtype.ext; simp
      right_inv := by intro D; apply Subtype.ext; simp }
  let deletedEquiv : {D : PlayerDeletion B H J p qDelete //
        summaryJ D = msgJ ∧ z ∈ D.1} ≃
      {D : PlayerDeletion B H K p qDelete //
        summaryK D = msgK ∧ edgeEquiv z ∈ D.1} :=
    { toFun := fun D ↦ ⟨deletionEquiv D.1, by
          refine ⟨?_, ?_⟩
          · change summaryK (deletionEquiv D.1) =
              summaryK (deletionEquiv deleted)
            rw [hsummary D.1, hsummary deleted]
            exact D.2.1
          · exact (mem_playerDeletionEquivOfPartEq_iff
              B H J K p qDelete hpart D.1 z).2 D.2.2⟩
      invFun := fun D ↦ ⟨deletionEquiv.symm D.1, by
          refine ⟨?_, ?_⟩
          · have hD := hsummary (deletionEquiv.symm D.1)
            have href := hsummary deleted
            rw [deletionEquiv.apply_symm_apply] at hD
            change summaryJ (deletionEquiv.symm D.1) = summaryJ deleted
            rw [← hD, ← href]
            exact D.2.1
          · have hmem := (mem_playerDeletionEquivOfPartEq_iff
              B H J K p qDelete hpart (deletionEquiv.symm D.1) z).1
              (by simpa using D.2.2)
            exact hmem⟩
      left_inv := by intro D; apply Subtype.ext; simp
      right_inv := by intro D; apply Subtype.ext; simp }
  have hfiberSubtype :
      Fintype.card {D : PlayerDeletion B H J p qDelete //
          summaryJ D = msgJ} =
        Fintype.card {D : PlayerDeletion B H K p qDelete //
          summaryK D = msgK} :=
    Fintype.card_congr fiberEquiv
  have hdeletedSubtype :
      Fintype.card {D : PlayerDeletion B H J p qDelete //
          summaryJ D = msgJ ∧ z ∈ D.1} =
        Fintype.card {D : PlayerDeletion B H K p qDelete //
          summaryK D = msgK ∧ edgeEquiv z ∈ D.1} :=
    Fintype.card_congr deletedEquiv
  have hfiberJ :
      (UniformPosterior.fiber summaryJ msgJ).card =
        Fintype.card {D : PlayerDeletion B H J p qDelete //
          summaryJ D = msgJ} := by
    unfold UniformPosterior.fiber
    exact (fintype_card_subtype_eq_filter_card
      (fun D : PlayerDeletion B H J p qDelete ↦ summaryJ D = msgJ)).symm
  have hfiberK :
      (UniformPosterior.fiber summaryK msgK).card =
        Fintype.card {D : PlayerDeletion B H K p qDelete //
          summaryK D = msgK} := by
    unfold UniformPosterior.fiber
    exact (fintype_card_subtype_eq_filter_card
      (fun D : PlayerDeletion B H K p qDelete ↦ summaryK D = msgK)).symm
  have hdeletedJ :
      (FixedCardPosterior.deletedFiber qDelete summaryJ msgJ z).card =
        Fintype.card {D : PlayerDeletion B H J p qDelete //
          summaryJ D = msgJ ∧ z ∈ D.1} := by
    rw [FixedCardPosterior.deletedFiber_eq_filter]
    exact (fintype_card_subtype_eq_filter_card
      (fun D : PlayerDeletion B H J p qDelete ↦
        summaryJ D = msgJ ∧ z ∈ D.1)).symm
  have hdeletedK :
      (FixedCardPosterior.deletedFiber qDelete summaryK msgK
          (edgeEquiv z)).card =
        Fintype.card {D : PlayerDeletion B H K p qDelete //
          summaryK D = msgK ∧ edgeEquiv z ∈ D.1} := by
    rw [FixedCardPosterior.deletedFiber_eq_filter]
    exact (fintype_card_subtype_eq_filter_card
      (fun D : PlayerDeletion B H K p qDelete ↦
        summaryK D = msgK ∧ edgeEquiv z ∈ D.1)).symm
  have hfiber :
      (Compression.fixedCardFiber qDelete schemeJ msgJ).card =
        (Compression.fixedCardFiber qDelete schemeK msgK).card := by
    calc
      _ = (UniformPosterior.fiber summaryJ msgJ).card :=
        (FixedCardPosterior.fiber_card_eq qDelete summaryJ prot.initial msgJ).symm
      _ = _ := hfiberJ.trans (hfiberSubtype.trans hfiberK.symm)
      _ = _ :=
        FixedCardPosterior.fiber_card_eq qDelete summaryK prot.initial msgK
  have hdeleted :
      (Compression.fixedCardDeletedFiber qDelete schemeJ msgJ z).card =
        (Compression.fixedCardDeletedFiber qDelete schemeK msgK
          (edgeEquiv z)).card := by
    calc
      _ = (FixedCardPosterior.deletedFiber qDelete summaryJ msgJ z).card :=
        (FixedCardPosterior.deletedFiber_card_eq qDelete summaryJ
          prot.initial msgJ z).symm
      _ = _ := hdeletedJ.trans (hdeletedSubtype.trans hdeletedK.symm)
      _ = _ := FixedCardPosterior.deletedFiber_card_eq qDelete summaryK
        prot.initial msgK (edgeEquiv z)
  change z ∈ Compression.belongSet
      (Compression.fixedCardDist qDelete hqJ) schemeJ delta msgJ ↔
    edgeEquiv z ∈ Compression.belongSet
      (Compression.fixedCardDist qDelete hqK) schemeK delta msgK
  rw [Compression.mem_belongSet_fixedCard_iff,
    Compression.mem_belongSet_fixedCard_iff, hfiber, hdeleted]

theorem player_expected_belongSet_le_forty
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete bits : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (history : List prot.Message) (hprot : prot.UsesCommunication bits)
    (delta : ℝ)
    (hq0 : 0 < qDelete)
    (hqlt : qDelete < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hqhalf : 2 * qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hbudget : Real.log (Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1) ≤
      (bits : ℝ) * Real.log 2)
    (hdelta : delta =
      (qDelete : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p}) :
    (FixedCard.uniform qDelete hqlt.le).expect (fun deleted ↦
        ((playerBelongSet B H J p qDelete hqlt.le prot history delta
          deleted).card : ℝ)) ≤
      40 * (bits : ℝ) * Real.log 2 / delta := by
  set_option maxHeartbeats 1000000 in
    exact FixedCardPosterior.uniform_expected_belongSet_le_forty
      qDelete bits (playerMessageSummary B H J p qDelete prot history)
      prot.initial delta hq0 hqlt hqhalf hprot.messageCard_le hbudget hdelta

theorem player_expected_belongSet_le_bits_log_succ
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete bits : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (history : List prot.Message) (hprot : prot.UsesCommunication bits)
    (delta : ℝ)
    (hq0 : 0 < qDelete)
    (hqlt : qDelete < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hqhalf : 2 * qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hdelta : delta =
      (qDelete : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p}) :
    (FixedCard.uniform qDelete hqlt.le).expect (fun deleted ↦
        ((playerBelongSet B H J p qDelete hqlt.le prot history delta
          deleted).card : ℝ)) ≤
      (20 / delta) * ((bits : ℝ) * Real.log 2 +
        Real.log (Fintype.card
          {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1)) := by
  exact FixedCardPosterior.uniform_expected_belongSet_le_bits_log_succ
    qDelete bits (playerMessageSummary B H J p qDelete prot history)
    prot.initial delta hq0 hqlt hqhalf hprot.messageCard_le hdelta

theorem player_sum_belongSet_le_bits_log_succ
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete bits : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (history : List prot.Message) (hprot : prot.UsesCommunication bits)
    (delta : ℝ)
    (hq0 : 0 < qDelete)
    (hqlt : qDelete < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hqhalf : 2 * qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hdelta : delta =
      (qDelete : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p}) :
    (∑ deleted : PlayerDeletion B H J p qDelete,
        ((playerBelongSet B H J p qDelete hqlt.le prot history delta
          deleted).card : ℝ)) ≤
      Fintype.card (PlayerDeletion B H J p qDelete) *
        ((20 / delta) * ((bits : ℝ) * Real.log 2 +
          Real.log (Fintype.card
            {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1))) := by
  letI : Nonempty (PlayerDeletion B H J p qDelete) :=
    FixedCard.nonempty qDelete hqlt.le
  have hcomp := player_expected_belongSet_le_bits_log_succ
    B H J p qDelete bits prot history hprot delta hq0 hqlt hqhalf hdelta
  change
    (FiniteDist.uniform (PlayerDeletion B H J p qDelete)).expect
        (fun deleted ↦ ((playerBelongSet B H J p qDelete hqlt.le prot
          history delta deleted).card : ℝ)) ≤ _ at hcomp
  rw [FiniteDist.uniform_expect] at hcomp
  have hcardPos : (0 : ℝ) <
      Fintype.card (PlayerDeletion B H J p qDelete) := by positivity
  calc
    _ ≤ ((20 / delta) * ((bits : ℝ) * Real.log 2 +
        Real.log (Fintype.card
          {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1))) *
        Fintype.card (PlayerDeletion B H J p qDelete) :=
      (div_le_iff hcardPos).1 hcomp
    _ = _ := by ring

theorem player_expected_posteriorBelong_le_forty
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) (qDelete bits : ℕ)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message]
    (history : List prot.Message) (hprot : prot.UsesCommunication bits)
    {eta : ℚ}
    (heta : (eta : ℝ) =
      ((qDelete : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p}) / 2)
    (hq0 : 0 < qDelete)
    (hqlt : qDelete < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hqhalf : 2 * qDelete ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p})
    (hbudget : Real.log (Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1) ≤
      (bits : ℝ) * Real.log 2) :
    (FixedCard.uniform qDelete hqlt.le).expect (fun deleted ↦
        ((UniformPosterior.belongingEdges eta
          (playerMessageSummary B H J p qDelete prot history)
          (fun D z ↦ z ∉ D.1)
          (playerMessageSummary B H J p qDelete prot history deleted)).card : ℝ)) ≤
      40 * (bits : ℝ) * Real.log 2 /
        ((qDelete : ℝ) /
          Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
            z ∈ part B H J p}) := by
  apply FixedCardPosterior.uniform_expected_posteriorBelong_le_forty
    qDelete bits (playerMessageSummary B H J p qDelete prot history)
    prot.initial heta hq0 hqlt hqhalf hprot.messageCard_le hbudget rfl

theorem mem_potentialSpecialEdges_iff_exists_liftEdge
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t)
    (e : Edge (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)) :
    e ∈ potentialSpecialEdges B H J ↔
      ∃ z : BaseEdge (L := L0) (R := R0) B,
        e = liftEdge z ∧ IsSpecial B H J z := by
  classical
  unfold potentialSpecialEdges AugmentedExpansion.specialEdges
  rw [AugmentedExpansion.liftEdges, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, rfl, by simpa [IsSpecial] using hz⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, by simpa [IsSpecial] using hz, rfl⟩

noncomputable def localSpecialEdges
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P) :
    Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} := by
  classical
  exact Finset.univ.filter fun z ↦ IsSpecial B H J z.1

noncomputable def playerRecoverableSpecialEdges
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (sample : Sample B H deletions)
    (p : Fin B.P) :
    Finset {z : BaseEdge (L := L0) (R := R0) B //
      z ∈ part B H sample.1 p} :=
  playerBelongSet B H sample.1 p (deletions p) (by
      simpa using hdeletions sample.1 p) prot
      (playerReferenceHistory B H deletions sample.1 sample.2 prot p)
      ((deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H sample.1 p})
      (sample.2 p) ∩
    localSpecialEdges B H sample.1 p

noncomputable def localPotentialSpecialEdges
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (suffix : SuffixIndexTuple B t p) :
    Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} := by
  classical
  exact Finset.univ.filter fun z ↦
    IsSpecial B H (completeWithSuffix p J suffix) z.1

noncomputable def conditionedPlayerRecoverableSpecialEdges
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    Finset {z : BaseEdge (L := L0) (R := R0) B //
      z ∈ part B H (prefixRepresentative B H p pref) p} :=
  playerBelongSet B H (prefixRepresentative B H p pref) p (deletions p)
      (by simpa using hdeletions (prefixRepresentative B H p pref) p) prot
      (playerReferenceHistory B H deletions
        (prefixRepresentative B H p pref)
        (representativeDeletionProfile B H deletions p pref through later)
        prot p)
      ((deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H (prefixRepresentative B H p pref) p})
      (through ⟨p, le_rfl⟩) ∩
    localPotentialSpecialEdges B H (prefixRepresentative B H p pref) p suffix

noncomputable def conditionedPlayerBelongSet
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P)
    (pref : PrefixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    Finset {z : BaseEdge (L := L0) (R := R0) B //
      z ∈ part B H (prefixRepresentative B H p pref) p} :=
  playerBelongSet B H (prefixRepresentative B H p pref) p (deletions p)
    (by simpa using hdeletions (prefixRepresentative B H p pref) p) prot
    (playerReferenceHistory B H deletions
      (prefixRepresentative B H p pref)
      (representativeDeletionProfile B H deletions p pref through later)
      prot p)
    ((deletions p : ℝ) /
      Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
        z ∈ part B H (prefixRepresentative B H p pref) p})
    (through ⟨p, le_rfl⟩)

theorem conditionedPlayerRecoverableSpecialEdges_eq
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    conditionedPlayerRecoverableSpecialEdges B H deletions hdeletions prot
        p pref suffix through later =
      conditionedPlayerBelongSet B H deletions hdeletions prot
          p pref through later ∩
        localPotentialSpecialEdges B H (prefixRepresentative B H p pref) p
          suffix := by
  rfl

theorem playerRecoverableSpecialEdges_card_reindexed
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (p : Fin B.P)
    (pref : PrefixIndexTuple B t p) (suffix : SuffixIndexTuple B t p)
    (through : ThroughDeletionProfile B H deletions p pref)
    (later : LaterDeletionProfile B H deletions p pref) :
    (playerRecoverableSpecialEdges B H deletions hdeletions prot
      (reindexedSample B H deletions p pref suffix through later) p).card =
      (conditionedPlayerRecoverableSpecialEdges B H deletions hdeletions prot
        p pref suffix through later).card := by
  classical
  let J := combinePrefixSuffix B p pref suffix
  let J0 := prefixRepresentative B H p pref
  let rep := representativeDeletionProfile B H deletions p pref through later
  let profileEquiv :=
    deletionProfileEquivPrefixRepresentative B H deletions p pref suffix
  let actual : DeletionProfile B H deletions J := profileEquiv.symm rep
  have hpart : part B H J p = part B H J0 p := by
    exact part_eq_prefixRepresentative_of_le B H p pref suffix p le_rfl
  let edgeEquiv := playerEdgeEquivOfPartEq B H J J0 p hpart
  have hprofile : profileEquiv actual = rep := by
    exact profileEquiv.apply_symm_apply rep
  have hhistory :
      playerReferenceHistory B H deletions J actual prot p =
        playerReferenceHistory B H deletions J0 rep prot p := by
    apply playerReferenceHistory_eq_of_agreeBefore B H deletions p
      J J0 actual rep prot
    · simpa [J, J0, prefixRepresentative] using
        (agreeBefore_combinePrefixSuffix B p pref suffix
          (fun _ ↦ ⟨0, H.t_pos⟩))
    · intro i hip
      have hpres := deletionEdges_profileEquivPrefixRepresentative_of_le
        B H deletions p pref suffix actual i hip.le
      rw [hprofile] at hpres
      exact hpres.symm
  have hcurrent :
      playerDeletionEquivOfPartEq B H J J0 p (deletions p) hpart
          (actual p) = through ⟨p, le_rfl⟩ := by
    have hc := congrFun hprofile p
    dsimp only [profileEquiv] at hc
    rw [deletionProfileEquivPrefixRepresentative_apply_of_le
      B H deletions p pref suffix actual p le_rfl] at hc
    have hrep : rep p = through ⟨p, le_rfl⟩ := by
      exact representativeDeletionProfile_through
        B H deletions p pref through later ⟨p, le_rfl⟩
    have hc' := hc.trans hrep
    convert hc' using 1
  have hcard : Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} =
      Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} :=
    Fintype.card_congr edgeEquiv
  have hdelta :
      (deletions p : ℝ) /
          Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
            z ∈ part B H J p} =
        (deletions p : ℝ) /
          Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
            z ∈ part B H J0 p} := by
    rw [hcard]
  have hfinset : edgeEquiv.finsetCongr
        (playerRecoverableSpecialEdges B H deletions hdeletions prot
          (⟨J, actual⟩ : Sample B H deletions) p) =
      conditionedPlayerRecoverableSpecialEdges B H deletions hdeletions prot
        p pref suffix through later := by
    ext y
    rw [edgeEquiv.finsetCongr_apply, Finset.mem_map_equiv]
    let x := edgeEquiv.symm y
    have htransport :=
      mem_playerBelongSet_playerEdgeEquivOfPartEq_iff
        B H J J0 p (deletions p) hpart
        (by rw [Fintype.card_coe]; exact hdeletions J p)
        (by rw [Fintype.card_coe]; exact hdeletions J0 p) prot
        (playerReferenceHistory B H deletions J actual prot p)
        (playerReferenceHistory B H deletions J0 rep prot p) hhistory
        ((deletions p : ℝ) /
          Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
            z ∈ part B H J p}) (actual p) x
    have hright :
        playerEdgeEquivOfPartEq B H J J0 p hpart x ∈
            playerBelongSet B H J0 p (deletions p)
              (by rw [Fintype.card_coe]; exact hdeletions J0 p) prot
              (playerReferenceHistory B H deletions J0 rep prot p)
              ((deletions p : ℝ) /
                Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                  z ∈ part B H J p})
              (playerDeletionEquivOfPartEq B H J J0 p (deletions p) hpart
                (actual p)) ↔
          playerEdgeEquivOfPartEq B H J J0 p hpart x ∈
            playerBelongSet B H J0 p (deletions p)
              (by rw [Fintype.card_coe]; exact hdeletions J0 p) prot
              (playerReferenceHistory B H deletions J0 rep prot p)
              ((deletions p : ℝ) /
                Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                  z ∈ part B H J0 p})
              (through ⟨p, le_rfl⟩) := by
      rw [hdelta, hcurrent]
    have htransport' := htransport.trans hright
    have hspecial : IsSpecial B H J x.1 ↔
        IsSpecial B H (completeWithSuffix p J0 suffix) (edgeEquiv x).1 := by
      rw [completeWithSuffix_prefixRepresentative B H p pref suffix]
      rfl
    rw [playerRecoverableSpecialEdges,
      conditionedPlayerRecoverableSpecialEdges,
      Finset.mem_inter, Finset.mem_inter]
    simp only [localSpecialEdges, localPotentialSpecialEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [x, J, J0, rep] using and_congr htransport' hspecial
  change
    (playerRecoverableSpecialEdges B H deletions hdeletions prot
      (⟨J, actual⟩ : Sample B H deletions) p).card = _
  calc
    _ = (edgeEquiv.finsetCongr
        (playerRecoverableSpecialEdges B H deletions hdeletions prot
          (⟨J, actual⟩ : Sample B H deletions) p)).card := by
      rw [edgeEquiv.finsetCongr_apply, Finset.card_map]
    _ = _ := congrArg Finset.card hfinset

theorem sum_through_playerBelongSet_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (hprot : prot.UsesCommunication bits)
    (p : Fin B.P) (pref : PrefixIndexTuple B t p)
    (later : LaterDeletionProfile B H deletions p pref)
    (rate logBound : ℝ) (hrate0 : 0 < rate)
    (hpart : (part B H (prefixRepresentative B H p pref) p).Nonempty)
    (hq0 : 0 < deletions p)
    (hqhalf : 2 * deletions p ≤ Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B //
        z ∈ part B H (prefixRepresentative B H p pref) p})
    (hrate : rate ≤ (deletions p : ℝ) /
      Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
        z ∈ part B H (prefixRepresentative B H p pref) p})
    (hlog : Real.log (Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H (prefixRepresentative B H p pref) p} + 1) ≤
      logBound) :
    (∑ through : ThroughDeletionProfile B H deletions p pref,
        ((playerBelongSet B H (prefixRepresentative B H p pref) p
          (deletions p)
          (by simpa using
            hdeletions (prefixRepresentative B H p pref) p) prot
          (playerReferenceHistory B H deletions
            (prefixRepresentative B H p pref)
            (representativeDeletionProfile B H deletions p pref through later)
            prot p)
          ((deletions p : ℝ) /
            Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H (prefixRepresentative B H p pref) p})
          (through ⟨p, le_rfl⟩)).card : ℝ)) ≤
      Fintype.card (ThroughDeletionProfile B H deletions p pref) *
        ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound)) := by
  classical
  let J0 := prefixRepresentative B H p pref
  let current : ThroughPlayers B p := ⟨p, le_rfl⟩
  let X := fun i : ThroughPlayers B p ↦
    PlayerDeletion B H J0 i.1 (deletions i.1)
  let split := Equiv.piSplitAt current X
  have hm0 : 0 < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hpart
  have hqlt : deletions p < Fintype.card
      {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} := by
    have hqhalf' : 2 * deletions p ≤ Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} := by
      simpa [J0] using hqhalf
    omega
  letI : Nonempty (X current) := FixedCard.nonempty (deletions p) hqlt.le
  let referenceDeletion : X current := Classical.choice inferInstance
  have hpoint
      (other : ∀ i : {i : ThroughPlayers B p // i ≠ current}, X i.1) :
      (∑ deleted : X current,
          ((playerBelongSet B H J0 p (deletions p) hqlt.le prot
            (playerReferenceHistory B H deletions J0
              (representativeDeletionProfile B H deletions p pref
                (split.symm (referenceDeletion, other)) later) prot p)
            ((deletions p : ℝ) /
              Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                z ∈ part B H J0 p}) deleted).card : ℝ)) ≤
        Fintype.card (X current) *
          ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound)) := by
    have hraw := player_sum_belongSet_le_bits_log_succ
      B H J0 p (deletions p) bits prot
      (playerReferenceHistory B H deletions J0
        (representativeDeletionProfile B H deletions p pref
          (split.symm (referenceDeletion, other)) later) prot p)
      hprot
      ((deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J0 p}) hq0 hqlt hqhalf rfl
    have hdeltaPos : 0 < (deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J0 p} := by positivity
    have hfactor : 20 /
          ((deletions p : ℝ) /
            Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H J0 p}) ≤ 20 / rate := by
      exact div_le_div_of_nonneg_left (by norm_num) hrate0 hrate
    have hlocalNonneg : 0 ≤ (bits : ℝ) * Real.log 2 +
        Real.log (Fintype.card
          {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} + 1) := by
      have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have hlogLocal : 0 ≤ Real.log (Fintype.card
          {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J0 p} + 1) :=
        Real.log_nonneg (by norm_num)
      positivity
    have htargetNonneg : 0 ≤ (bits : ℝ) * Real.log 2 + logBound := by
      linarith
    have hterm : (20 /
          ((deletions p : ℝ) /
            Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H J0 p})) *
          ((bits : ℝ) * Real.log 2 + Real.log (Fintype.card
            {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H J0 p} + 1)) ≤
        (20 / rate) * ((bits : ℝ) * Real.log 2 + logBound) := by
      exact mul_le_mul hfactor (by linarith) hlocalNonneg (by positivity)
    exact hraw.trans (mul_le_mul_of_nonneg_left hterm (by positivity))
  calc
    (∑ through : ThroughDeletionProfile B H deletions p pref,
        ((playerBelongSet B H J0 p (deletions p) _ prot
          (playerReferenceHistory B H deletions J0
            (representativeDeletionProfile B H deletions p pref through later)
            prot p)
          ((deletions p : ℝ) /
            Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H J0 p}) (through current)).card : ℝ)) =
        ∑ data : X current ×
            (∀ i : {i : ThroughPlayers B p // i ≠ current}, X i.1),
          ((playerBelongSet B H J0 p (deletions p) _ prot
            (playerReferenceHistory B H deletions J0
              (representativeDeletionProfile B H deletions p pref
                (split.symm data) later) prot p)
            ((deletions p : ℝ) /
              Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                z ∈ part B H J0 p}) data.1).card : ℝ) := by
      symm
      apply Fintype.sum_equiv split.symm
      intro data
      simp [split]
    _ = ∑ other : (∀ i : {i : ThroughPlayers B p // i ≠ current}, X i.1),
        ∑ deleted : X current,
          ((playerBelongSet B H J0 p (deletions p) _ prot
            (playerReferenceHistory B H deletions J0
              (representativeDeletionProfile B H deletions p pref
                (split.symm (deleted, other)) later) prot p)
            ((deletions p : ℝ) /
              Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                z ∈ part B H J0 p}) deleted).card : ℝ) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ other : (∀ i : {i : ThroughPlayers B p // i ≠ current}, X i.1),
        ∑ deleted : X current,
          ((playerBelongSet B H J0 p (deletions p) _ prot
            (playerReferenceHistory B H deletions J0
              (representativeDeletionProfile B H deletions p pref
                (split.symm (referenceDeletion, other)) later) prot p)
            ((deletions p : ℝ) /
              Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
                z ∈ part B H J0 p}) deleted).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro other _hother
      apply Finset.sum_congr rfl
      intro deleted _hdeleted
      have hhistory := playerReferenceHistory_eq_of_agreeBefore B H deletions p
        J0 J0
        (representativeDeletionProfile B H deletions p pref
          (split.symm (deleted, other)) later)
        (representativeDeletionProfile B H deletions p pref
          (split.symm (referenceDeletion, other)) later) prot
        (by intro _ _; rfl) (by
          intro i hip
          apply congrArg deletionEdges
          rw [representativeDeletionProfile_through B H deletions p pref
              (split.symm (deleted, other)) later ⟨i, hip.le⟩,
            representativeDeletionProfile_through B H deletions p pref
              (split.symm (referenceDeletion, other)) later ⟨i, hip.le⟩]
          have hine : (⟨i, hip.le⟩ : ThroughPlayers B p) ≠ current := by
            intro hieq
            have hiv := congrArg Subtype.val hieq
            exact (ne_of_lt hip) hiv
          simp [split, Equiv.piSplitAt, hine])
      rw [hhistory]
    _ ≤ ∑ _other : (∀ i : {i : ThroughPlayers B p // i ≠ current}, X i.1),
        Fintype.card (X current) *
          ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound)) := by
      apply Finset.sum_le_sum
      intro other _hother
      exact hpoint other
    _ = Fintype.card (ThroughDeletionProfile B H deletions p pref) *
        ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hcardSplit := Fintype.card_congr split
      rw [Fintype.card_prod] at hcardSplit
      rw [hcardSplit]
      push_cast
      ring

theorem sum_suffix_recoverableSpecial_le_for_assembly
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (recoverable :
      Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    (∑ suffix : SuffixIndexTuple B t p,
        ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
      Fintype.card (SuffixIndexTuple B t p) *
        (((B.P : ℝ) / t) * recoverable.card) := by
  classical
  have hprob (z : {z : BaseEdge (L := L0) (R := R0) B //
      z ∈ part B H J p}) :
      (SpecialEdges.uniformSuffixDistribution B H p).prob
          (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) ≤
        (B.P : ℝ) / t := by
    obtain ⟨K, hKprefix, hzK⟩ := (mem_part_iff B H J p z.1).1 z.2
    have hcomplete (suffix : SuffixIndexTuple B t p) :
        completeWithSuffix p K suffix = completeWithSuffix p J suffix := by
      funext i
      by_cases hpi : p ≤ i
      · simp [completeWithSuffix, hpi]
      · have hip : i < p := lt_of_not_ge hpi
        simp [completeWithSuffix, hpi, hKprefix i hip]
    have hevent :
        (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
          SpecialEdges.SuffixMakesSpecial B H p K z.1 := by
      funext suffix
      apply propext
      simp [localPotentialSpecialEdges, hcomplete suffix,
        SpecialEdges.suffixMakesSpecial_iff]
    have hfilter :
        Finset.univ.filter
            (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
          Finset.univ.filter (SpecialEdges.SuffixMakesSpecial B H p K z.1) := by
      ext suffix
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (z ∈ localPotentialSpecialEdges B H J p suffix) ↔
        SpecialEdges.SuffixMakesSpecial B H p K z.1 suffix
      exact iff_of_eq (congrFun hevent suffix)
    calc
      (SpecialEdges.uniformSuffixDistribution B H p).prob
          (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
          (SpecialEdges.uniformSuffixDistribution B H p).prob
            (SpecialEdges.SuffixMakesSpecial B H p K z.1) := by
              unfold FiniteDist.prob
              rw [hfilter]
      _ ≤ (B.P : ℝ) / t :=
        SpecialEdges.uniform_suffix_special_prob_le B H p K z.1 hzK
  have hexpect :
      (SpecialEdges.uniformSuffixDistribution B H p).expect (fun suffix ↦
          ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
        ((B.P : ℝ) / t) * recoverable.card := by
    apply FiniteDist.expect_inter_card_le
    intro z _hz
    exact hprob z
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (SuffixIndexTuple B t p) := inferInstance
  change
    (FiniteDist.uniform (SuffixIndexTuple B t p)).expect (fun suffix ↦
      ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
        ((B.P : ℝ) / t) * recoverable.card at hexpect
  rw [FiniteDist.uniform_expect] at hexpect
  have hcardPos : (0 : ℝ) < Fintype.card (SuffixIndexTuple B t p) := by
    positivity
  calc
    _ ≤ (((B.P : ℝ) / t) * recoverable.card) *
        Fintype.card (SuffixIndexTuple B t p) :=
      (div_le_iff hcardPos).1 hexpect
    _ = _ := by ring

set_option maxHeartbeats 4000000

theorem sum_playerRecoverableSpecialEdges_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (hprot : prot.UsesCommunication bits)
    (p : Fin B.P) (rate logBound : ℝ) (hrate0 : 0 < rate)
    (hlogBound0 : 0 ≤ logBound)
    (hpositive : ∀ J p, (part B H J p).Nonempty → 0 < deletions p)
    (hhalf : ∀ J p, (part B H J p).Nonempty →
      2 * deletions p ≤ (part B H J p).card)
    (hrate : ∀ J p, (part B H J p).Nonempty →
      rate ≤ (deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p})
    (hlog : ∀ J p, (part B H J p).Nonempty →
      Real.log (Fintype.card
        {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p} + 1) ≤
        logBound) :
    (∑ sample : Sample B H deletions,
        ((playerRecoverableSpecialEdges B H deletions hdeletions prot
          sample p).card : ℝ)) ≤
      Fintype.card (Sample B H deletions) *
        (((B.P : ℝ) / t) *
          ((20 / rate) * ((bits : ℝ) * Real.log 2 + logBound))) := by
  classical
  let lambda : ℝ := (B.P : ℝ) / t
  let compression : ℝ :=
    (20 / rate) * ((bits : ℝ) * Real.log 2 + logBound)
  have hlambda : 0 ≤ lambda := by positivity
  have hreindex := sum_sample_eq_prefix_suffix_through_later
    B H deletions p (fun sample ↦
      ((playerRecoverableSpecialEdges B H deletions hdeletions prot
        sample p).card : ℝ))
  rw [hreindex]
  change
    (∑ pref : PrefixIndexTuple B t p,
      ∑ suffix : SuffixIndexTuple B t p,
        ∑ through : ThroughDeletionProfile B H deletions p pref,
          ∑ later : LaterDeletionProfile B H deletions p pref,
            ((playerRecoverableSpecialEdges B H deletions hdeletions prot
              (reindexedSample B H deletions p pref suffix through later) p).card : ℝ)) ≤ _
  simp_rw [playerRecoverableSpecialEdges_card_reindexed
    B H deletions hdeletions prot p]
  calc
    (∑ pref : PrefixIndexTuple B t p,
      ∑ suffix : SuffixIndexTuple B t p,
        ∑ through : ThroughDeletionProfile B H deletions p pref,
          ∑ later : LaterDeletionProfile B H deletions p pref,
            ((conditionedPlayerRecoverableSpecialEdges B H deletions
              hdeletions prot p pref suffix through later).card : ℝ)) =
        ∑ pref : PrefixIndexTuple B t p,
          ∑ through : ThroughDeletionProfile B H deletions p pref,
            ∑ later : LaterDeletionProfile B H deletions p pref,
              ∑ suffix : SuffixIndexTuple B t p,
                ((conditionedPlayerRecoverableSpecialEdges B H deletions
                  hdeletions prot p pref suffix through later).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro pref _hpref
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro through _hthrough
      rw [Finset.sum_comm]
    _ ≤ ∑ pref : PrefixIndexTuple B t p,
          ∑ through : ThroughDeletionProfile B H deletions p pref,
            ∑ later : LaterDeletionProfile B H deletions p pref,
              Fintype.card (SuffixIndexTuple B t p) *
                (lambda * (conditionedPlayerBelongSet B H deletions
                  hdeletions prot p pref through later).card) := by
      apply Finset.sum_le_sum
      intro pref _hpref
      apply Finset.sum_le_sum
      intro through _hthrough
      apply Finset.sum_le_sum
      intro later _hlater
      simpa [conditionedPlayerRecoverableSpecialEdges_eq, lambda] using
        (sum_suffix_recoverableSpecial_le_for_assembly B H
          (prefixRepresentative B H p pref) p
          (conditionedPlayerBelongSet B H deletions hdeletions prot
            p pref through later))
    _ = ∑ pref : PrefixIndexTuple B t p,
          ∑ later : LaterDeletionProfile B H deletions p pref,
            (Fintype.card (SuffixIndexTuple B t p) * lambda) *
              (∑ through : ThroughDeletionProfile B H deletions p pref,
                ((conditionedPlayerBelongSet B H deletions hdeletions prot
                  p pref through later).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro pref _hpref
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro later _hlater
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ ∑ pref : PrefixIndexTuple B t p,
          ∑ _later : LaterDeletionProfile B H deletions p pref,
            (Fintype.card (SuffixIndexTuple B t p) * lambda) *
              (Fintype.card
                (ThroughDeletionProfile B H deletions p pref) * compression) := by
      apply Finset.sum_le_sum
      intro pref _hpref
      apply Finset.sum_le_sum
      intro later _hlater
      by_cases hpart :
          (part B H (prefixRepresentative B H p pref) p).Nonempty
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [conditionedPlayerBelongSet, compression] using
          (sum_through_playerBelongSet_le B H deletions hdeletions prot hprot
            p pref later rate logBound hrate0 hpart
            (hpositive (prefixRepresentative B H p pref) p hpart)
            (by
              rw [Fintype.card_coe]
              exact hhalf (prefixRepresentative B H p pref) p hpart)
            (hrate (prefixRepresentative B H p pref) p hpart)
            (hlog (prefixRepresentative B H p pref) p hpart))
      · have hempty : Fintype.card
            {z : BaseEdge (L := L0) (R := R0) B //
              z ∈ part B H (prefixRepresentative B H p pref) p} = 0 := by
          rw [Fintype.card_coe, Finset.card_eq_zero]
          exact Finset.not_nonempty_iff_eq_empty.mp hpart
        have hzero (through : ThroughDeletionProfile B H deletions p pref) :
            (conditionedPlayerBelongSet B H deletions hdeletions prot
              p pref through later).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro z _hz
          exact hpart ⟨z.1, z.2⟩
        simp_rw [hzero]
        have hcompression : 0 ≤ compression := by
          have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
          dsimp [compression]
          positivity
        simp only [Nat.cast_zero, Finset.sum_const_zero]
        have hsuffix : 0 ≤
            (Fintype.card (SuffixIndexTuple B t p) : ℝ) := by positivity
        have hthrough : 0 ≤
            (Fintype.card
              (ThroughDeletionProfile B H deletions p pref) : ℝ) := by
          positivity
        simpa only [mul_zero] using
          (mul_nonneg (mul_nonneg hsuffix hlambda)
            (mul_nonneg hthrough hcompression))
    _ = Fintype.card (Sample B H deletions) * (lambda * compression) := by
      have hindex := Fintype.card_congr
        (indexTupleEquivPrefixSuffix (t := t) B p)
      rw [Fintype.card_prod] at hindex
      have hprofile (pref : PrefixIndexTuple B t p) :
          Fintype.card (ThroughDeletionProfile B H deletions p pref) *
              Fintype.card (LaterDeletionProfile B H deletions p pref) =
            deletionFiberCard B r t deletions := by
        have hc := Fintype.card_congr
          (deletionProfileEquivThroughLater B H deletions p pref)
        rw [Fintype.card_prod,
          deletionProfile_card B H deletions
            (prefixRepresentative B H p pref)] at hc
        exact hc.symm
      have hcount :
          (∑ pref : PrefixIndexTuple B t p,
            Fintype.card (LaterDeletionProfile B H deletions p pref) *
              (Fintype.card (SuffixIndexTuple B t p) *
                Fintype.card (ThroughDeletionProfile B H deletions p pref))) =
            Fintype.card (Sample B H deletions) := by
        calc
          _ = ∑ _pref : PrefixIndexTuple B t p,
              Fintype.card (SuffixIndexTuple B t p) *
                deletionFiberCard B r t deletions := by
            apply Finset.sum_congr rfl
            intro pref _hpref
            rw [← hprofile pref]
            ring
          _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              sample_card B H deletions, hindex]
            simp only [Nat.cast_id]
            ac_rfl
      calc
        (∑ pref : PrefixIndexTuple B t p,
            ∑ _later : LaterDeletionProfile B H deletions p pref,
              (Fintype.card (SuffixIndexTuple B t p) * lambda) *
                (Fintype.card
                  (ThroughDeletionProfile B H deletions p pref) * compression)) =
            ∑ pref : PrefixIndexTuple B t p,
              Fintype.card (LaterDeletionProfile B H deletions p pref) *
                (Fintype.card (SuffixIndexTuple B t p) * lambda *
                  (Fintype.card (ThroughDeletionProfile B H deletions p pref) *
                    compression)) := by
          apply Finset.sum_congr rfl
          intro pref _hpref
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ = ∑ pref : PrefixIndexTuple B t p,
              ((Fintype.card (LaterDeletionProfile B H deletions p pref) *
                (Fintype.card (SuffixIndexTuple B t p) *
                  Fintype.card (ThroughDeletionProfile B H deletions p pref)) : ℕ) : ℝ) *
                (lambda * compression) := by
          apply Finset.sum_congr rfl
          intro pref _hpref
          push_cast
          ring
        _ = ((∑ pref : PrefixIndexTuple B t p,
              Fintype.card (LaterDeletionProfile B H deletions p pref) *
                (Fintype.card (SuffixIndexTuple B t p) *
                  Fintype.card (ThroughDeletionProfile B H deletions p pref)) : ℕ) : ℝ) *
              (lambda * compression) := by
          rw [Nat.cast_sum, Finset.sum_mul]
        _ = _ := by
          rw [hcount]
    _ = _ := by rfl

set_option maxHeartbeats 1000000

theorem globalRecoverableSpecial_card_le_sum_player
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B))
    [DecidableEq prot.Message] (sample : Sample B H deletions)
    {eta : ℚ} (rate : ℝ)
    (hpositive : ∀ J p, (part B H J p).Nonempty → 0 < deletions p)
    (hrate : ∀ J p, (part B H J p).Nonempty →
      rate ≤ (deletions p : ℝ) /
        Fintype.card {z : BaseEdge (L := L0) (R := R0) B //
          z ∈ part B H J p})
    (hetaRate : (eta : ℝ) ≤ rate / 2) :
    (UniformPosterior.belongingEdges eta
        (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot sample) ∩
      potentialSpecialEdges B H sample.1).card ≤
      ∑ p : Fin B.P,
        (playerRecoverableSpecialEdges B H deletions hdeletions prot
          sample p).card := by
  classical
  let global := UniformPosterior.belongingEdges eta
      (protocolSummary B H deletions prot)
      (finitePartitionDistribution B H deletions hdeletions).graphPresent
      (protocolSummary B H deletions prot sample) ∩
    potentialSpecialEdges B H sample.1
  let localAug := fun p : Fin B.P ↦
    liftEdges ((playerRecoverableSpecialEdges B H deletions hdeletions prot
      sample p).image Subtype.val)
  have hsubset : global ⊆ Finset.univ.biUnion localAug := by
    intro e he
    have he' := he
    change e ∈ UniformPosterior.belongingEdges eta
        (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot sample) ∩
      potentialSpecialEdges B H sample.1 at he'
    rcases Finset.mem_inter.1 he' with ⟨hbelongsSet, hpotential⟩
    obtain ⟨z, rfl, hspecial⟩ :=
      (mem_potentialSpecialEdges_iff_exists_liftEdge B H sample.1 e).1
        hpotential
    obtain ⟨p, hzpart⟩ :=
      (SimpleExpansion.mem_graph_iff B H sample.1 z).1 hspecial.1
    have hpartNonempty : (part B H sample.1 p).Nonempty := ⟨z, hzpart⟩
    have hq0 : 0 < deletions p := hpositive sample.1 p hpartNonempty
    have hrateLocal := hrate sample.1 p hpartNonempty
    have hetaLocal : (eta : ℝ) ≤
        ((deletions p : ℝ) /
          Fintype.card {w : BaseEdge (L := L0) (R := R0) B //
            w ∈ part B H sample.1 p}) / 2 := by
      linarith
    have hbelongs : UniformPosterior.Belongs eta
        (protocolSummary B H deletions prot)
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (protocolSummary B H deletions prot sample) (liftEdge z) :=
      (UniformPosterior.mem_belongingEdges_iff _ _ _ _ _).1 hbelongsSet
    have hlocal := globalBelongs_imp_mem_playerBelongSet
      B H deletions hdeletions prot sample p z hzpart
      ((deletions p : ℝ) /
        Fintype.card {w : BaseEdge (L := L0) (R := R0) B //
          w ∈ part B H sample.1 p}) hetaLocal hbelongs
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_univ p, ?_⟩
    change liftEdge z ∈ liftEdges
      ((playerRecoverableSpecialEdges B H deletions hdeletions prot
        sample p).image Subtype.val)
    rw [AugmentedExpansion.mem_liftEdges_iff, Finset.mem_image]
    refine ⟨⟨z, hzpart⟩, ?_, rfl⟩
    rw [playerRecoverableSpecialEdges, Finset.mem_inter]
    exact ⟨hlocal, by simp [localSpecialEdges, hspecial]⟩
  calc
    global.card ≤ (Finset.univ.biUnion localAug).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ p : Fin B.P, (localAug p).card := Finset.card_biUnion_le
    _ = ∑ p : Fin B.P,
        (playerRecoverableSpecialEdges B H deletions hdeletions prot
          sample p).card := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [AugmentedExpansion.liftEdges_card]
      apply Finset.card_image_iff.mpr
      intro x _hx y _hy hxy
      exact Subtype.ext hxy

set_option maxHeartbeats 1000000

theorem uniformSuffix_localPotentialSpecial_prob_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (z : {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    (SpecialEdges.uniformSuffixDistribution B H p).prob
        (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) ≤
      (B.P : ℝ) / t := by
  classical
  obtain ⟨K, hKprefix, hzK⟩ := (mem_part_iff B H J p z.1).1 z.2
  have hcomplete (suffix : SuffixIndexTuple B t p) :
      completeWithSuffix p K suffix = completeWithSuffix p J suffix := by
    funext i
    by_cases hpi : p ≤ i
    · simp [completeWithSuffix, hpi]
    · have hip : i < p := lt_of_not_ge hpi
      simp [completeWithSuffix, hpi, hKprefix i hip]
  have hevent :
      (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
        SpecialEdges.SuffixMakesSpecial B H p K z.1 := by
    funext suffix
    apply propext
    simp [localPotentialSpecialEdges, hcomplete suffix,
      SpecialEdges.suffixMakesSpecial_iff]
  have hfilter :
      Finset.univ.filter
          (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
        Finset.univ.filter (SpecialEdges.SuffixMakesSpecial B H p K z.1) := by
    ext suffix
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (z ∈ localPotentialSpecialEdges B H J p suffix) ↔
      SpecialEdges.SuffixMakesSpecial B H p K z.1 suffix
    exact iff_of_eq (congrFun hevent suffix)
  calc
    (SpecialEdges.uniformSuffixDistribution B H p).prob
        (fun suffix ↦ z ∈ localPotentialSpecialEdges B H J p suffix) =
        (SpecialEdges.uniformSuffixDistribution B H p).prob
          (SpecialEdges.SuffixMakesSpecial B H p K z.1) := by
            unfold FiniteDist.prob
            rw [hfilter]
    _ ≤ (B.P : ℝ) / t :=
      SpecialEdges.uniform_suffix_special_prob_le B H p K z.1 hzK

theorem uniformSuffix_recoverableSpecial_expect_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (recoverable :
      Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    (SpecialEdges.uniformSuffixDistribution B H p).expect (fun suffix ↦
        ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
      ((B.P : ℝ) / t) * recoverable.card := by
  apply FiniteDist.expect_inter_card_le
  intro z _hz
  exact uniformSuffix_localPotentialSpecial_prob_le B H J p z

theorem sum_suffix_recoverableSpecial_le
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (J : IndexTuple B t) (p : Fin B.P)
    (recoverable :
      Finset {z : BaseEdge (L := L0) (R := R0) B // z ∈ part B H J p}) :
    (∑ suffix : SuffixIndexTuple B t p,
        ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
      Fintype.card (SuffixIndexTuple B t p) *
        (((B.P : ℝ) / t) * recoverable.card) := by
  letI : Nonempty (Fin t) := ⟨⟨0, H.t_pos⟩⟩
  letI : Nonempty (SuffixIndexTuple B t p) := inferInstance
  have h := uniformSuffix_recoverableSpecial_expect_le B H J p recoverable
  change
    (FiniteDist.uniform (SuffixIndexTuple B t p)).expect (fun suffix ↦
      ((recoverable ∩ localPotentialSpecialEdges B H J p suffix).card : ℝ)) ≤
        ((B.P : ℝ) / t) * recoverable.card at h
  rw [FiniteDist.uniform_expect] at h
  have hcardPos : (0 : ℝ) < Fintype.card (SuffixIndexTuple B t p) := by
    positivity
  calc
    _ ≤ (((B.P : ℝ) / t) * recoverable.card) *
        Fintype.card (SuffixIndexTuple B t p) :=
      (div_le_iff hcardPos).1 h
    _ = _ := by ring

set_option maxHeartbeats 200000

noncomputable def protocolPosteriorModel
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (cert : ∀ sample : Sample B H deletions,
      MatchingGapCertificate (edgePartition sample).graph)
    (hcertSpecial : ∀ sample, (cert sample).special = special sample)
    (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)) :
    FinitePartitionDistribution.ProtocolPosteriorModel
      (finitePartitionDistribution B H deletions hdeletions) cert prot where
  Summary := IndexTuple B t × prot.TranscriptCode
  summaryFintype := inferInstance
  summaryDecidableEq := Classical.decEq _
  summary := protocolSummary B H deletions prot
  output := fun data ↦ prot.outputFromTranscriptCode data.2
  relevant := fun data ↦ potentialSpecialEdges B H data.1
  output_eq := by
    intro sample
    exact prot.outputFromTranscriptCode_transcriptCode (edgePartition sample)
  relevant_on_output := by
    intro sample hpresent
    change
      prot.outputFromTranscriptCode
          (prot.transcriptCode (edgePartition sample)) ⊆
        (edgePartition sample).graph.edges at hpresent
    rw [prot.outputFromTranscriptCode_transcriptCode] at hpresent
    change
      prot.outputFromTranscriptCode
          (prot.transcriptCode (edgePartition sample)) ∩
          potentialSpecialEdges B H sample.1 =
        prot.result (edgePartition sample) ∩ (cert sample).special
    rw [prot.outputFromTranscriptCode_transcriptCode]
    rw [hcertSpecial sample]
    apply (inter_special_eq_inter_potentialSpecialEdges sample ?_).symm
    rw [← edgePartition_graph]
    exact hpresent

end HardDistribution

namespace FinitePartitionDistribution

variable {P : ℕ} {L R : Type*}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem isHardForCommunication_of_posterior_recovery
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    {q s : ℕ} {rho eta beta : ℚ}
    (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hgap : ∀ x : D.Sample,
      (((cert x).ordinaryUpper + q : ℕ) : ℚ) <
        rho * (cert x).optimumLower)
    (model : ∀ (prot : BlackboardProtocol P L R),
      prot.UsesCommunication s → ProtocolPosteriorModel D cert prot)
    (hbelongingSum : ∀ (prot : BlackboardProtocol P L R)
      (hprot : prot.UsesCommunication s),
      let W := model prot hprot
      let _ : Fintype W.Summary := W.summaryFintype
      let _ : DecidableEq W.Summary := W.summaryDecidableEq
      (∑ x : D.Sample,
        ((UniformPosterior.belongingEdges eta W.summary D.graphPresent
          (W.summary x) ∩ W.relevant (W.summary x)).card : ℚ)) ≤
        beta * (q + 1) * Fintype.card D.Sample) :
    D.IsHardForCommunication rho (1 - eta + beta) s := by
  apply D.isHardForCommunication_of_success_many_special cert hrho hgap
  intro prot hprot
  let W := model prot hprot
  letI : Fintype W.Summary := W.summaryFintype
  letI : DecidableEq W.Summary := W.summaryDecidableEq
  letI : DecidableEq D.Sample := Classical.decEq D.Sample
  have hmanyBelonging :
      ((UniformPosterior.manyBelongingRelevantSamples eta W.summary
        D.graphPresent W.relevant q).card : ℚ) ≤
          beta * Fintype.card D.Sample := by
    apply UniformPosterior.manyBelongingRelevant_card_le_of_sum
    simpa [W] using hbelongingSum prot hprot
  have hposterior := UniformPosterior.feasible_many_relevant_card_le
    heta1 W.summary D.graphPresent W.output W.relevant q hmanyBelonging
  have hsubset :
      D.successfulManySpecialSamples cert q rho prot ⊆
        UniformPosterior.feasibleManyRelevantSamples eta W.summary
          D.graphPresent W.output W.relevant q := by
    intro x hx
    have hxdata : prot.SucceedsOn rho (D.input x) ∧
        D.DiscoversManySpecial cert q prot x := by
      simpa [successfulManySpecialSamples] using hx
    have hpresent : W.output (W.summary x) ⊆ (D.input x).graph.edges := by
      rw [W.output_eq x]
      exact hxdata.1.1.1
    simp only [UniformPosterior.feasibleManyRelevantSamples,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨W.feasible_of_succeeds x hxdata.1,
      (W.hasManyRelevant_iff_discoversManySpecial q x hpresent).2 hxdata.2⟩
  have hcard := Finset.card_le_card hsubset
  exact le_trans (by exact_mod_cast hcard) hposterior

end FinitePartitionDistribution

namespace HardDistribution

open SimpleExpansion AugmentedExpansion

variable {L0 R0 : Type} {r t : ℕ}
  [Fintype L0] [Fintype R0] [DecidableEq L0] [DecidableEq R0]

def RecoverableSpecialSumBound
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (cert : ∀ sample : Sample B H deletions,
      MatchingGapCertificate (edgePartition sample).graph)
    (hcertSpecial : ∀ sample, (cert sample).special = special sample)
    (bits threshold : ℕ) (eta beta : ℚ) : Prop :=
  ∀ (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)),
    prot.UsesCommunication bits →
    let W := protocolPosteriorModel B H deletions hdeletions cert
      hcertSpecial prot
    let _ : Fintype W.Summary := W.summaryFintype
    let _ : DecidableEq W.Summary := W.summaryDecidableEq
    (∑ sample : Sample B H deletions,
      ((UniformPosterior.belongingEdges eta W.summary
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (W.summary sample) ∩ W.relevant (W.summary sample)).card : ℚ)) ≤
      beta * (threshold + 1) * Fintype.card (Sample B H deletions)

def ExactRecoverableSpecialSumBound
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (bits threshold : ℕ) (eta beta : ℚ) : Prop :=
  ∀ (prot : BlackboardProtocol (B.P + 1)
      (AugmentedExpansion.Left (L := L0) (R := R0) B)
      (AugmentedExpansion.Right (L := L0) (R := R0) B)),
    prot.UsesCommunication bits →
    let W := protocolPosteriorModel B H deletions hdeletions
      (fun sample ↦ exactSampleCertificate sample) (fun _ ↦ rfl) prot
    let _ : Fintype W.Summary := W.summaryFintype
    let _ : DecidableEq W.Summary := W.summaryDecidableEq
    (∑ sample : Sample B H deletions,
      ((UniformPosterior.belongingEdges eta W.summary
        (finitePartitionDistribution B H deletions hdeletions).graphPresent
        (W.summary sample) ∩ W.relevant (W.summary sample)).card : ℚ)) ≤
      beta * (threshold + 1) * Fintype.card (Sample B H deletions)

theorem communicationHardness_of_recoverableSpecialSum
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    (cert : ∀ sample : Sample B H deletions,
      MatchingGapCertificate (edgePartition sample).graph)
    (hcertSpecial : ∀ sample, (cert sample).special = special sample)
    {threshold bits : ℕ} {rho eta beta : ℚ}
    (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hgap : ∀ sample : Sample B H deletions,
      (((cert sample).ordinaryUpper + threshold : ℕ) : ℚ) <
        rho * (cert sample).optimumLower)
    (hsum : RecoverableSpecialSumBound B H deletions hdeletions cert
      hcertSpecial bits threshold eta beta) :
    (finitePartitionDistribution B H deletions hdeletions).IsHardForCommunication
      rho (1 - eta + beta) bits := by
  apply FinitePartitionDistribution.isHardForCommunication_of_posterior_recovery
    (finitePartitionDistribution B H deletions hdeletions) cert
    heta1 hrho hgap
    (fun prot _hprot ↦
      protocolPosteriorModel B H deletions hdeletions cert hcertSpecial prot)
  intro prot hprot
  exact hsum prot hprot

theorem communicationHardness_of_exactRecoverableSpecialSum
    (B : SimpleProperBlueprint) (H : ERSGraph L0 R0 B.C r t)
    (deletions : Fin B.P → ℕ)
    (hdeletions : ∀ J p, deletions p ≤ (part B H J p).card)
    {threshold bits : ℕ} {rho eta beta : ℚ}
    (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hgap : ∀ sample : Sample B H deletions,
      (((exactSampleCertificate sample).ordinaryUpper + threshold : ℕ) : ℚ) <
        rho * (exactSampleCertificate sample).optimumLower)
    (hsum : ExactRecoverableSpecialSumBound B H deletions hdeletions
      bits threshold eta beta) :
    (finitePartitionDistribution B H deletions hdeletions).IsHardForCommunication
      rho (1 - eta + beta) bits := by
  apply FinitePartitionDistribution.isHardForCommunication_of_posterior_recovery
    (finitePartitionDistribution B H deletions hdeletions)
    (fun sample ↦ exactSampleCertificate sample) heta1 hrho hgap
    (fun prot _hprot ↦
      protocolPosteriorModel B H deletions hdeletions
        (fun sample ↦ exactSampleCertificate sample) (fun _ ↦ rfl) prot)
  intro prot hprot
  exact hsum prot hprot

end HardDistribution

end Formal.Streaming
