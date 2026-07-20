import SemiStreamingMatching.Proofs.Blueprint.ConstructionCounting
import SemiStreamingMatching.Proofs.Blueprint.ConstructionEstimate

open scoped BigOperators

namespace PaperWalkEncoding

theorem encodedData_card_formula_aux (S D H : ℕ) :
    Fintype.card (EncodedData S D H) =
      D * S * 2 ^ H * freeMultiplicity S D H := by
  rw [Fintype.card_sigma]
  have hterm (d : Fin D) :
      Fintype.card (Fin S × (Fin H → Bool) × FreeData S D H d) =
        S * 2 ^ H * freeMultiplicity S D H := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, card_FreeData]
    ring
  simp_rw [hterm]
  rw [Fin.sum_const]
  simp
  ring

theorem alphabet_power_formula_aux (S D H : ℕ) :
    alphabetSize S D ^ parameterCount D H =
      D * S * 2 ^ H * freeMultiplicity S D H := by
  calc
    alphabetSize S D ^ parameterCount D H =
        Fintype.card (Vertex (parameterCount D H) (alphabetSize S D)) := by simp
    _ = Fintype.card (EncodedData S D H) :=
      Fintype.card_congr (vertexEncodedEquiv S D H)
    _ = _ := encodedData_card_formula_aux S D H

theorem card_leftClass_central {N S D H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j t : ℕ)
    (ht : H ≤ t) (htD : t < D) :
    (leftClass (D := D) (H := H) initial j t).card =
      (leftWordClass (H := H) initial j).card * freeMultiplicity S D H := by
  calc
    (leftClass (D := D) (H := H) initial j t).card =
        Fintype.card {v // v ∈ leftClass (D := D) (H := H) initial j t} := by simp
    _ = Fintype.card (CentralFiber initial j t ht htD) :=
      Fintype.card_congr (leftClassCentralFiberEquiv initial j t ht htD)
    _ = (leftWordClass (H := H) initial j).card * freeMultiplicity S D H := by
      rw [Fintype.card_sigma]
      simp_rw [card_FreeData]
      simp

theorem card_leftWordClass {N S H : ℕ}
    (initial : Fin S → GamblerWalk.State N) (j : ℕ) :
    (leftWordClass (H := H) initial j).card =
      ∑ s : Fin S, (GamblerWalk.ambientMaxZeroWords N H (initial s) j).card := by
  classical
  let e : {sw // sw ∈ leftWordClass (H := H) initial j} ≃
      Σ s : Fin S, {w : Fin H → Bool //
        w ∈ GamblerWalk.ambientMaxZeroWords N H (initial s) j} := {
    toFun := fun sw ↦ ⟨sw.1.1, sw.1.2, by
      simpa [GamblerWalk.ambientMaxZeroWords] using
        (mem_leftWordClass_iff initial j sw.1).mp sw.2⟩
    invFun := fun z ↦ ⟨(z.1, z.2.1), by
      apply (mem_leftWordClass_iff initial j _).mpr
      simpa [GamblerWalk.ambientMaxZeroWords] using
        (Finset.mem_filter.mp z.2.2).2⟩
    left_inv := fun sw ↦ by rfl
    right_inv := fun z ↦ by rfl }
  calc
    (leftWordClass (H := H) initial j).card =
        Fintype.card {sw // sw ∈ leftWordClass (H := H) initial j} :=
      (Fintype.card_coe (leftWordClass (H := H) initial j)).symm
    _ = Fintype.card (Σ s : Fin S, {w : Fin H → Bool //
          w ∈ GamblerWalk.ambientMaxZeroWords N H (initial s) j}) :=
      Fintype.card_congr e
    _ = ∑ s : Fin S, (GamblerWalk.ambientMaxZeroWords N H (initial s) j).card := by
      rw [Fintype.card_sigma]
      simp

theorem finiteMaxMass_eq_leftWordClass_density (m K k j : ℕ) :
    PaperConstructionEstimate.finiteMaxMass m K k j =
      ((leftWordClass (H := k * K) (StartDistribution.start m) j).card : ℝ) /
        ((StartDistribution.sampleCount m : ℕ) * (2 : ℝ) ^ (k * K)) := by
  rw [PaperConstructionEstimate.finiteMaxMass, card_leftWordClass]
  unfold GamblerWalk.ambientMaxZeroProbability
  rw [← Finset.sum_div]
  push_cast
  ring

theorem leftClass_density_eq_finiteMaxMass_div {m K k D j t : ℕ}
    (hD : 0 < D) (ht : k * K ≤ t) (htD : t < D) :
    (((leftClass (D := D) (H := k * K) (StartDistribution.start m) j t).card : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          (parameterCount D (k * K)) : ℕ) =
      PaperConstructionEstimate.finiteMaxMass m K k j / D := by
  rw [card_leftClass_central (StartDistribution.start m) j t ht htD,
    alphabet_power_formula_aux,
    finiteMaxMass_eq_leftWordClass_density]
  have hS : (0 : ℝ) < StartDistribution.sampleCount m := by
    exact_mod_cast StartDistribution.sampleCount_pos m
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k * K) := by positivity
  have hfreeNat : 0 < freeMultiplicity (StartDistribution.sampleCount m) D (k * K) := by
    have hSnat := StartDistribution.sampleCount_pos m
    unfold freeMultiplicity
    positivity
  have hfree : (0 : ℝ) < freeMultiplicity
      (StartDistribution.sampleCount m) D (k * K) := by exact_mod_cast hfreeNat
  push_cast
  field_simp [ne_of_gt hS, ne_of_gt hDreal, ne_of_gt hpow, ne_of_gt hfree]
  ring

theorem classPairSize_density_eq_min_finiteMaxMass_div
    {m K k D t : ℕ} (j : maxLabel (2 * m))
    (hD : 0 < D) (ht : k * K ≤ t) (htD : t < D) :
    ((classPairSize (D := D) (H := k * K) (StartDistribution.start m) j t : ℕ) : ℝ) /
        ((alphabetSize (StartDistribution.sampleCount m) D) ^
          (parameterCount D (k * K)) : ℕ) =
      min (PaperConstructionEstimate.finiteMaxMass m K k (maxLabelValue j))
          (PaperConstructionEstimate.finiteMaxMass m K k (2 * m - maxLabelValue j)) / D := by
  let total : ℝ :=
    ((alphabetSize (StartDistribution.sampleCount m) D) ^
      (parameterCount D (k * K)) : ℕ)
  let a : ℝ := PaperConstructionEstimate.finiteMaxMass m K k (maxLabelValue j)
  let b : ℝ :=
    PaperConstructionEstimate.finiteMaxMass m K k (2 * m - maxLabelValue j)
  let L : ℕ :=
    (leftClass (D := D) (H := k * K) (StartDistribution.start m)
      (maxLabelValue j) t).card
  let R : ℕ :=
    (leftClass (D := D) (H := k * K) (StartDistribution.start m)
      (2 * m - maxLabelValue j) t).card
  have htotal : 0 < total := by
    have hSpos := StartDistribution.sampleCount_pos m
    have hAlpha : 0 < alphabetSize (StartDistribution.sampleCount m) D := by
      rw [alphabetSize_eq]
      positivity
    have hpowNat : 0 <
        alphabetSize (StartDistribution.sampleCount m) D ^ parameterCount D (k * K) :=
      pow_pos hAlpha _
    dsimp [total]
    exact_mod_cast hpowNat
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hL : (L : ℝ) / total = a / D := by
    exact leftClass_density_eq_finiteMaxMass_div hD ht htD
  have hR : (R : ℝ) / total = b / D := by
    exact leftClass_density_eq_finiteMaxMass_div hD ht htD
  have hright :
      (rightClass (D := D) (H := k * K) (StartDistribution.start m)
        (2 * m - maxLabelValue j) t).card = R := by
    exact (card_leftClass_eq_card_rightClass (D := D) (H := k * K)
      (StartDistribution.start m) (2 * m - maxLabelValue j) t).symm
  unfold classPairSize
  rw [hright]
  change ((min L R : ℕ) : ℝ) / total = min a b / D
  by_cases hab : a ≤ b
  · have hcardsR : (L : ℝ) ≤ R := by
      apply (div_le_div_right htotal).mp
      rw [hL, hR]
      exact (div_le_div_right hDreal).mpr hab
    have hcards : L ≤ R := by exact_mod_cast hcardsR
    rw [Nat.min_eq_left hcards, min_eq_left hab, hL]
  · have hba : b ≤ a := le_of_not_ge hab
    have hcardsR : (R : ℝ) ≤ L := by
      apply (div_le_div_right htotal).mp
      rw [hR, hL]
      exact (div_le_div_right hDreal).mpr hba
    have hcards : R ≤ L := by exact_mod_cast hcardsR
    rw [Nat.min_eq_right hcards, min_eq_right hba, hR]

end PaperWalkEncoding
