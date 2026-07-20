import SemiStreamingMatching.Proofs.Blueprint.ConstructionResult
import SemiStreamingMatching.Proofs.Blueprint.UpperBound

theorem exists_blueprint_value_near_two_thirds :
    ∀ ε : ℝ, 0 < ε →
      ∃ B : SimpleProperBlueprint, (2 : ℝ) / 3 - ε < B.value :=
  exists_blueprint_value_near_two_thirds_proof

theorem blueprint_value_le_two_thirds (B : SimpleProperBlueprint) :
    B.value ≤ (2 : ℝ) / 3 :=
  blueprint_value_le_two_thirds_proof B

theorem two_thirds_is_lub :
    IsLUB {x : ℝ | ∃ B : SimpleProperBlueprint, x = B.value} ((2 : ℝ) / 3) :=
  two_thirds_is_lub_of_near_of_upper
    exists_blueprint_value_near_two_thirds
    blueprint_value_le_two_thirds
