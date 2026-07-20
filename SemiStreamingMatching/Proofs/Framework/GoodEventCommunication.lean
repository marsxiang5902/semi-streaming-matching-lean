import SemiStreamingMatching.Proofs.Framework.CommunicationHardness
import SemiStreamingMatching.Proofs.Framework.SpecialEdgeLowerBound

namespace Formal.Streaming

open scoped BigOperators

namespace FinitePartitionDistribution

variable {P : ℕ} {L R : Type*}
  [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem successfulManySpecial_card_le_of_posterior_recovery
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    {q s : ℕ} {rho eta beta : ℚ}
    (heta1 : eta ≤ 1)
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
    ∀ (prot : BlackboardProtocol P L R) (_hprot : prot.UsesCommunication s),
      ((D.successfulManySpecialSamples cert q rho prot).card : ℚ) ≤
        (1 - eta + beta) * Fintype.card D.Sample := by
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
  exact le_trans (by exact_mod_cast Finset.card_le_card hsubset) hposterior

theorem isHardForCommunication_of_good_posterior_recovery
    (D : FinitePartitionDistribution P L R)
    (cert : ∀ x : D.Sample, MatchingGapCertificate (D.input x).graph)
    (Good : D.Sample → Prop)
    {q s : ℕ} {rho eta beta pBad : ℚ}
    (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hgap : ∀ x : D.Sample, Good x →
      (((cert x).ordinaryUpper + q : ℕ) : ℚ) <
        rho * (cert x).optimumLower)
    (hbad : ((D.badSamples Good).card : ℚ) ≤
      pBad * Fintype.card D.Sample)
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
    D.IsHardForCommunication rho (pBad + (1 - eta + beta)) s := by
  apply D.isHardForCommunication_of_good_success_many_special
    cert Good hrho hgap hbad
  exact D.successfulManySpecial_card_le_of_posterior_recovery cert
    heta1 model hbelongingSum

end FinitePartitionDistribution

end Formal.Streaming
