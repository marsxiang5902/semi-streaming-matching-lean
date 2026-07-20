import SemiStreamingMatching.Proofs.Blueprint.Blueprint

theorem exists_blueprint_value_gt_half_of_near
    (hnear : ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε < B.value) :
    ∃ B : SimpleProperBlueprint, (1 : ℝ) / 2 < B.value := by
  obtain ⟨B, hB⟩ := hnear (1 / 12 : ℝ) (by norm_num)
  refine ⟨B, ?_⟩
  norm_num at hB ⊢
  linarith

theorem exists_blueprint_value_optimal_of_near
    (hnear : ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε < B.value) :
    ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε ≤ B.value := by
  intro ε hε
  obtain ⟨B, hB⟩ := hnear ε hε
  exact ⟨B, hB.le⟩

theorem two_thirds_is_lub_of_near_of_upper
    (hnear : ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε < B.value)
    (hupper : ∀ B : SimpleProperBlueprint, B.value ≤ (2 : ℝ) / 3) :
    IsLUB {x : ℝ | ∃ B : SimpleProperBlueprint, x = B.value} ((2 : ℝ) / 3) := by
  constructor
  · rintro x ⟨B, rfl⟩
    exact hupper B
  · intro b hb
    by_contra hnot
    have hlt : b < (2 : ℝ) / 3 := lt_of_not_ge hnot
    let ε : ℝ := (2 : ℝ) / 3 - b
    have hε : 0 < ε := sub_pos.mpr hlt
    obtain ⟨B, hB⟩ := hnear ε hε
    have hBb : b < B.value := by
      simpa [ε] using hB
    exact (not_lt_of_ge (hb ⟨B, rfl⟩)) hBb
