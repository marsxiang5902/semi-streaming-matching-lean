import SemiStreamingMatching.Proofs.Blueprint.CentralCard
import SemiStreamingMatching.Proofs.Blueprint.ConstructionEstimate
import SemiStreamingMatching.Proofs.Blueprint.ParameterSelection
import SemiStreamingMatching.Proofs.Blueprint.ResultLogic

open scoped BigOperators

namespace PaperConstructionResult

open GamblerWalk
open PaperWalkEncoding
open PaperConstructionEstimate

theorem sum_maxLabel_eq_sum_Ico {N : ℕ} (f : ℕ → ℝ) :
    (∑ j : maxLabel N, f (maxLabelValue j)) =
      ∑ j in Finset.Ico 1 N, f j := by
  have hset : Finset.Ico 1 N =
      (Finset.range (N - 1)).image (fun i : ℕ ↦ i + 1) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hi
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  change (∑ j : Fin (N - 1), f (j.1 + 1)) = _
  calc
    (∑ j : Fin (N - 1), f (j.1 + 1)) =
        ∑ i in Finset.range (N - 1), f (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1)) (N - 1)
    _ = ∑ j in Finset.Ico 1 N, f j := by
      rw [hset, Finset.sum_image]
      intro a _ b _ hab
      omega

theorem min_finiteMaxMass_lower {m K k j : ℕ} (hm : 0 < m)
    (hNK : 2 * m ≤ K) (hj : 1 ≤ j) (hjtop : j < 2 * m) :
    StartDistribution.maxMass m j - failureRatio K ^ k ≤
      min (finiteMaxMass m K k j) (finiteMaxMass m K k (2 * m - j)) := by
  have hleftAbs := finiteMaxMass_approx_maxMass (k := k) hNK hj hjtop
  have hj' : 1 ≤ 2 * m - j := by omega
  have hj'top : 2 * m - j < 2 * m := by omega
  have hrightAbs := finiteMaxMass_approx_maxMass (k := k) hNK hj' hj'top
  have hsymm := StartDistribution.maxMass_symm hm hj hjtop
  have hleft : StartDistribution.maxMass m j - failureRatio K ^ k ≤
      finiteMaxMass m K k j := by
    have := (abs_le.mp hleftAbs).1
    linarith
  have hright : StartDistribution.maxMass m j - failureRatio K ^ k ≤
      finiteMaxMass m K k (2 * m - j) := by
    have h := (abs_le.mp hrightAbs).1
    rw [← hsymm] at h
    linarith
  exact le_min hleft hright

theorem sum_min_finiteMaxMass_lower {m K k : ℕ} (hm : 0 < m)
    (hNK : 2 * m ≤ K) :
    (2 * (m : ℝ)) / (3 * (m : ℝ) + 1) -
        2 * (m : ℝ) * failureRatio K ^ k ≤
      ∑ j : maxLabel (2 * m),
        min (finiteMaxMass m K k (maxLabelValue j))
          (finiteMaxMass m K k (2 * m - maxLabelValue j)) := by
  let δ : ℝ := failureRatio K ^ k
  have hpoint : ∀ j ∈ Finset.Ico 1 (2 * m),
      StartDistribution.maxMass m j - δ ≤
        min (finiteMaxMass m K k j) (finiteMaxMass m K k (2 * m - j)) := by
    intro j hj
    exact min_finiteMaxMass_lower hm hNK (Finset.mem_Ico.mp hj).1
      (Finset.mem_Ico.mp hj).2
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_sub_distrib, PaperConstructionEstimate.sum_maxMass_Ico hm] at hsum
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  rw [sum_maxLabel_eq_sum_Ico
    (fun j ↦ min (finiteMaxMass m K k j) (finiteMaxMass m K k (2 * m - j)))]
  have hcard : (((2 * m - 1 : ℕ) : ℝ)) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (by omega : 2 * m - 1 ≤ 2 * m)
  have hδ : 0 ≤ δ := pow_nonneg (failureRatio_nonneg K) k
  have herr : (2 * (m : ℝ)) * δ ≥ ((2 * m - 1 : ℕ) : ℝ) * δ :=
    mul_le_mul_of_nonneg_right hcard hδ
  dsimp [δ] at hsum ⊢
  linarith

def centralGroups (D H : ℕ) : Finset (Fin (parameterCount D H)) :=
  Finset.univ.filter fun p ↦ H + 2 ≤ p.1 ∧ p.1 < D + 2

def centralGroupEquiv {D H : ℕ} (hHD : H ≤ D) :
    {p // p ∈ centralGroups D H} ≃ Fin (D - H) where
  toFun p := ⟨p.1.1 - (H + 2), by
    have hp := (Finset.mem_filter.mp p.2).2
    omega⟩
  invFun i := ⟨⟨H + 2 + i.1, by
      simp only [parameterCount]
      omega⟩, by
    simp only [centralGroups, Finset.mem_filter, Finset.mem_univ, true_and]
    omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    have hp := (Finset.mem_filter.mp p.2).2
    simp only
    omega
  right_inv i := by
    apply Fin.ext
    simp only
    omega

theorem card_centralGroups {D H : ℕ} (hHD : H ≤ D) :
    (centralGroups D H).card = D - H := by
  calc
    (centralGroups D H).card = Fintype.card {p // p ∈ centralGroups D H} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Fin (D - H)) := Fintype.card_congr (centralGroupEquiv hHD)
    _ = D - H := Fintype.card_fin _

theorem group_classPair_density_eq_pairedMass_div
    {m K k D : ℕ} (hD : 0 < D)
    (p : Fin (parameterCount D (k * K)))
    (hpLower : k * K + 2 ≤ p.1) (hpUpper : p.1 < D + 2) :
    ((∑ j : maxLabel (2 * m),
        classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
          (p.1 - 2) : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          parameterCount D (k * K) : ℕ) =
      (∑ j : maxLabel (2 * m),
        min (finiteMaxMass m K k (maxLabelValue j))
          (finiteMaxMass m K k (2 * m - maxLabelValue j))) / D := by
  have ht : k * K ≤ p.1 - 2 := by omega
  have htD : p.1 - 2 < D := by omega
  calc
    ((∑ j : maxLabel (2 * m),
        classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
          (p.1 - 2) : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          parameterCount D (k * K) : ℕ) =
      ∑ j : maxLabel (2 * m),
        ((classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
          (p.1 - 2) : ℕ) : ℝ) /
          ((alphabetSize (StartDistribution.sampleCount m) D) ^
            parameterCount D (k * K) : ℕ) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ = ∑ j : maxLabel (2 * m),
        min (finiteMaxMass m K k (maxLabelValue j))
          (finiteMaxMass m K k (2 * m - maxLabelValue j)) / D := by
      apply Fintype.sum_congr
      intro j
      exact classPairSize_density_eq_min_finiteMaxMass_div j hD ht htD
    _ = (∑ j : maxLabel (2 * m),
        min (finiteMaxMass m K k (maxLabelValue j))
          (finiteMaxMass m K k (2 * m - maxLabelValue j))) / D := by
      rw [Finset.sum_div]

theorem central_sum_density_eq
    {m K k D : ℕ} (hD : 0 < D) (hHD : k * K ≤ D) :
    ((∑ p in centralGroups D (k * K),
        ∑ j : maxLabel (2 * m),
          classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
            (p.1 - 2) : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          parameterCount D (k * K) : ℕ) =
      (((D - k * K : ℕ) : ℝ) / D) *
        (∑ j : maxLabel (2 * m),
          min (finiteMaxMass m K k (maxLabelValue j))
            (finiteMaxMass m K k (2 * m - maxLabelValue j))) := by
  calc
    ((∑ p in centralGroups D (k * K),
        ∑ j : maxLabel (2 * m),
          classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
            (p.1 - 2) : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          parameterCount D (k * K) : ℕ) =
      ∑ p in centralGroups D (k * K),
        ((∑ j : maxLabel (2 * m),
          classPairSize (D := D) (H := k * K) (StartDistribution.start m) j
            (p.1 - 2) : ℕ) : ℝ) /
          ((alphabetSize (StartDistribution.sampleCount m) D) ^
            parameterCount D (k * K) : ℕ) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ = ∑ _p in centralGroups D (k * K),
        (∑ j : maxLabel (2 * m),
          min (finiteMaxMass m K k (maxLabelValue j))
            (finiteMaxMass m K k (2 * m - maxLabelValue j))) / D := by
      apply Finset.sum_congr rfl
      intro p hp
      have hv := (Finset.mem_filter.mp hp).2
      exact group_classPair_density_eq_pairedMass_div hD p hv.1 hv.2
    _ = (((D - k * K : ℕ) : ℝ) / D) *
        (∑ j : maxLabel (2 * m),
          min (finiteMaxMass m K k (maxLabelValue j))
            (finiteMaxMass m K k (2 * m - maxLabelValue j))) := by
      rw [Finset.sum_const, card_centralGroups hHD]
      push_cast
      ring

noncomputable def selectedBlueprint {ε : ℝ}
    (p : PaperParameterSelection.SelectedParameters ε) : SimpleProperBlueprint :=
  paperBlueprint (D := p.D) (H := p.k * p.K) (StartDistribution.start p.m)
    (by have := p.hm; omega) (StartDistribution.sampleCount_pos p.m) p.hDpos

theorem selected_central_density_le_value {ε : ℝ}
    (p : PaperParameterSelection.SelectedParameters ε) :
    (((p.D - 2 * p.H : ℕ) : ℝ) / p.D) *
        (∑ j : maxLabel (2 * p.m),
          min (finiteMaxMass p.m p.K p.k (maxLabelValue j))
            (finiteMaxMass p.m p.K p.k (2 * p.m - maxLabelValue j))) ≤
      (selectedBlueprint p).value := by
  let H := p.k * p.K
  let V : ℕ :=
    alphabetSize (StartDistribution.sampleCount p.m) p.D ^ parameterCount p.D H
  let paired : ℝ :=
    ∑ j : maxLabel (2 * p.m),
      min (finiteMaxMass p.m p.K p.k (maxLabelValue j))
        (finiteMaxMass p.m p.K p.k (2 * p.m - maxLabelValue j))
  have hH : p.H = H := by exact p.hH
  have hHD : H ≤ p.D := by
    rw [← hH]
    exact p.hHltD.le
  have hfiniteNonneg (j : ℕ) : 0 ≤ finiteMaxMass p.m p.K p.k j := by
    unfold finiteMaxMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro s _
      unfold GamblerWalk.ambientMaxZeroProbability
      exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    · exact Nat.cast_nonneg _
  have hpairNonneg : 0 ≤ paired := by
    apply Finset.sum_nonneg
    intro j _
    apply le_min
    · exact hfiniteNonneg (maxLabelValue j)
    · exact hfiniteNonneg (2 * p.m - maxLabelValue j)
  have hnat := central_classPairSize_sum_le_multiplicity_sum
    (D := p.D) (H := H) (StartDistribution.start p.m)
  change
      (∑ q in centralGroups p.D H,
          ∑ j : maxLabel (2 * p.m),
            classPairSize (D := p.D) (H := H) (StartDistribution.start p.m) j
              (q.1 - 2)) ≤
        ∑ q : Fin (parameterCount p.D H),
          (paperIndexedData (D := p.D) (H := H)
            (StartDistribution.start p.m) (by have := p.hm; omega)).edgeMultiplicity q at hnat
  have hnatReal :
      ((∑ q in centralGroups p.D H,
          ∑ j : maxLabel (2 * p.m),
            classPairSize (D := p.D) (H := H) (StartDistribution.start p.m) j
              (q.1 - 2) : ℕ) : ℝ) ≤
        ((∑ q : Fin (parameterCount p.D H),
          (paperIndexedData (D := p.D) (H := H)
            (StartDistribution.start p.m)
              (by have := p.hm; omega)).edgeMultiplicity q : ℕ) : ℝ) := by
    exact Nat.cast_le.mpr hnat
  have hdiv :
      ((∑ q in centralGroups p.D H,
          ∑ j : maxLabel (2 * p.m),
            classPairSize (D := p.D) (H := H) (StartDistribution.start p.m) j
              (q.1 - 2) : ℕ) : ℝ) / V ≤
        ((∑ q : Fin (parameterCount p.D H),
          (paperIndexedData (D := p.D) (H := H)
            (StartDistribution.start p.m)
              (by have := p.hm; omega)).edgeMultiplicity q : ℕ) : ℝ) / V :=
    div_le_div_of_nonneg_right hnatReal (by positivity)
  have hblueprint :
      ((∑ q : Fin (parameterCount p.D H),
          (paperIndexedData (D := p.D) (H := H)
            (StartDistribution.start p.m)
              (by have := p.hm; omega)).edgeMultiplicity q : ℕ) : ℝ) / V ≤
        (selectedBlueprint p).value := by
    exact paperBlueprint_value_lower (D := p.D) (H := H)
      (StartDistribution.start p.m) (by have := p.hm; omega)
      (StartDistribution.sampleCount_pos p.m) p.hDpos
  have hfull : (((p.D - H : ℕ) : ℝ) / p.D) * paired ≤
      (selectedBlueprint p).value := by
    rw [← central_sum_density_eq (m := p.m) (K := p.K) (k := p.k)
      p.hDpos hHD]
    exact hdiv.trans hblueprint
  have htwoH : 2 * H ≤ p.D := by
    rw [← hH]
    exact p.two_H_le_D
  have hsub : p.D - 2 * H ≤ p.D - H := by omega
  have hfactor : (((p.D - 2 * H : ℕ) : ℝ) / p.D) ≤
      (((p.D - H : ℕ) : ℝ) / p.D) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hsub
    · positivity
  rw [hH]
  exact (mul_le_mul_of_nonneg_right hfactor hpairNonneg).trans hfull

theorem paperLowerBound_le_of_central_density {ε : ℝ}
    (p : PaperParameterSelection.SelectedParameters ε)
    (B : SimpleProperBlueprint)
    (hcentral :
      (((p.D - 2 * p.H : ℕ) : ℝ) / p.D) *
          (∑ j : maxLabel (2 * p.m),
            min (finiteMaxMass p.m p.K p.k (maxLabelValue j))
              (finiteMaxMass p.m p.K p.k (2 * p.m - maxLabelValue j))) ≤
        B.value) :
    paperLowerBound p.m ≤ B.value := by
  let δ : ℝ := failureRatio p.K ^ p.k
  let a : ℝ := 1 - 1 / (p.m : ℝ)
  let M : ℝ := 2 * (p.m : ℝ) / (3 * (p.m : ℝ) + 1)
  have hsum := sum_min_finiteMaxMass_lower (k := p.k) p.hm p.hboundary
  change M - 2 * (p.m : ℝ) * δ ≤ _ at hsum
  have ha0 : 0 ≤ a := PaperParameterSelection.centralFactor_nonneg p.hm
  have ha1 : a ≤ 1 := PaperParameterSelection.centralFactor_le_one p.hm
  have hδ0 : 0 ≤ δ := pow_nonneg (failureRatio_nonneg p.K) p.k
  have hm0 : 0 ≤ (p.m : ℝ) := by positivity
  have haδ : a * δ ≤ δ := mul_le_of_le_one_left hδ0 ha1
  have htwom : 2 * (p.m : ℝ) * (a * δ) ≤
      2 * (p.m : ℝ) * δ :=
    mul_le_mul_of_nonneg_left haδ (by positivity)
  have herror :
      a * (M - δ) - 4 * (p.m : ℝ) * δ ≤
        a * (M - 2 * (p.m : ℝ) * δ) := by
    nlinarith [mul_nonneg hm0 hδ0]
  have hscaled : a * (M - 2 * (p.m : ℝ) * δ) ≤
      a * (∑ j : maxLabel (2 * p.m),
        min (finiteMaxMass p.m p.K p.k (maxLabelValue j))
          (finiteMaxMass p.m p.K p.k (2 * p.m - maxLabelValue j))) :=
    mul_le_mul_of_nonneg_left hsum ha0
  have hfactor : (((p.D - 2 * p.H : ℕ) : ℝ) / p.D) = a := by
    exact p.centralDelayFactor_eq
  have hpaper := p.paperLowerBound_le_central_estimate
  change paperLowerBound p.m ≤ a * (M - δ) - 4 * (p.m : ℝ) * δ at hpaper
  rw [hfactor] at hcentral
  exact hpaper.trans (herror.trans (hscaled.trans hcentral))

end PaperConstructionResult

theorem exists_blueprint_value_near_two_thirds_proof :
    ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε < B.value := by
  intro ε hε
  let p := Classical.choice
    (PaperParameterSelection.exists_selectedParameters ε hε)
  let B := PaperConstructionResult.selectedBlueprint p
  refine ⟨B, ?_⟩
  have hcentral := PaperConstructionResult.selected_central_density_le_value p
  have hlower := PaperConstructionResult.paperLowerBound_le_of_central_density
    p B hcentral
  exact p.hlower.trans_le hlower

theorem exists_blueprint_value_gt_half :
    ∃ B : SimpleProperBlueprint, (1 : ℝ) / 2 < B.value :=
  exists_blueprint_value_gt_half_of_near exists_blueprint_value_near_two_thirds_proof

theorem exists_blueprint_value_optimal :
    ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε ≤ B.value :=
  exists_blueprint_value_optimal_of_near exists_blueprint_value_near_two_thirds_proof
