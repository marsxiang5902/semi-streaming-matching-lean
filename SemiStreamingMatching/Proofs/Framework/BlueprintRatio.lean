import SemiStreamingMatching.Proofs.Blueprint.Blueprint

namespace Formal.Streaming

noncomputable def blueprintValueRat (B : SimpleProperBlueprint) : ℚ :=
  (B.edgeCount : ℚ) / (B.vertexCount : ℚ)

theorem blueprintValueRat_cast (B : SimpleProperBlueprint) :
    (blueprintValueRat B : ℝ) = B.value := by
  simp [blueprintValueRat, SimpleProperBlueprint.value]

theorem blueprintValueRat_nonneg (B : SimpleProperBlueprint) :
    0 ≤ blueprintValueRat B := by
  have h : (0 : ℝ) ≤ (blueprintValueRat B : ℝ) := by
    simpa only [blueprintValueRat_cast] using value_nonneg B
  exact_mod_cast h

theorem blueprintValueRat_le_one (B : SimpleProperBlueprint) :
    blueprintValueRat B ≤ 1 := by
  have h : (blueprintValueRat B : ℝ) ≤ 1 := by
    simpa only [blueprintValueRat_cast] using value_le_one B
  exact_mod_cast h

noncomputable def blueprintRatio (B : SimpleProperBlueprint) : ℝ :=
  (2 - 2 * B.value) / (2 - B.value)

noncomputable def blueprintRatioRat (B : SimpleProperBlueprint) : ℚ :=
  (2 - 2 * blueprintValueRat B) / (2 - blueprintValueRat B)

theorem blueprintRatioRat_cast (B : SimpleProperBlueprint) :
    (blueprintRatioRat B : ℝ) = blueprintRatio B := by
  simp [blueprintRatioRat, blueprintRatio, blueprintValueRat_cast]

theorem two_sub_value_pos (B : SimpleProperBlueprint) : 0 < 2 - B.value := by
  have h := value_le_one B
  linarith

theorem blueprintRatio_nonneg (B : SimpleProperBlueprint) : 0 ≤ blueprintRatio B := by
  rw [blueprintRatio]
  exact div_nonneg (by nlinarith [value_le_one B]) (two_sub_value_pos B).le

theorem blueprintRatio_le_one (B : SimpleProperBlueprint) : blueprintRatio B ≤ 1 := by
  rw [blueprintRatio]
  apply (div_le_one (two_sub_value_pos B)).2
  nlinarith [value_nonneg B]

theorem blueprintRatio_mul_two_sub_value (B : SimpleProperBlueprint) :
    blueprintRatio B * (2 - B.value) = 2 - 2 * B.value := by
  rw [blueprintRatio, div_mul_cancel₀]
  exact ne_of_gt (two_sub_value_pos B)

theorem blueprintRatio_mem_Icc (B : SimpleProperBlueprint) :
    blueprintRatio B ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨blueprintRatio_nonneg B, blueprintRatio_le_one B⟩

theorem perturbed_ratio_le {v η : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    (2 - 2 * v + η) / (2 - v - η) ≤
      (2 - 2 * v) / (2 - v) + 8 * η := by
  have hd : 0 < 2 - v := by linarith
  have hdη : 0 < 2 - v - η := by linarith
  have hfrac : (2 - 2 * v) / (2 - v) ≤ 1 := by
    apply (div_le_one hd).2
    linarith
  have hbracket :
      0 ≤ 8 * (2 - v) - 8 * η - 1 - (2 - 2 * v) / (2 - v) := by
    nlinarith
  have hid :
      ((2 - 2 * v) / (2 - v) + 8 * η) * (2 - v - η) -
          (2 - 2 * v + η) =
        η * (8 * (2 - v) - 8 * η - 1 - (2 - 2 * v) / (2 - v)) := by
    field_simp [ne_of_gt hd]
    ring
  apply (div_le_iff hdη).2
  nlinarith [mul_nonneg hη0 hbracket]

theorem perturbed_ratioRat_le {v η : ℚ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    (2 - 2 * v + η) / (2 - v - η) ≤
      (2 - 2 * v) / (2 - v) + 8 * η := by
  have hη1' : (η : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    exact_mod_cast hη1
  have hη1real : (η : ℝ) ≤ (1 / 2 : ℝ) := by
    norm_num at hη1' ⊢
    exact hη1'
  have hreal := perturbed_ratio_le
    (v := (v : ℝ)) (η := (η : ℝ))
    (by exact_mod_cast hv0) (by exact_mod_cast hv1)
    (by exact_mod_cast hη0) hη1real
  exact_mod_cast hreal

theorem blueprint_perturbed_ratioRat_le (B : SimpleProperBlueprint) {η : ℚ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    (2 - 2 * blueprintValueRat B + η) /
        (2 - blueprintValueRat B - η) ≤
      blueprintRatioRat B + 8 * η := by
  exact perturbed_ratioRat_le (blueprintValueRat_nonneg B)
    (blueprintValueRat_le_one B) hη0 hη1

end Formal.Streaming
