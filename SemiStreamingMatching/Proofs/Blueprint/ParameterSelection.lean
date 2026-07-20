import SemiStreamingMatching.Proofs.Blueprint.ConstructionEstimate
import SemiStreamingMatching.Proofs.Blueprint.Construction

open scoped BigOperators

namespace PaperParameterSelection

open GamblerWalk

structure SelectedParameters (ε : ℝ) where
  m : ℕ
  K : ℕ
  k : ℕ
  H : ℕ
  D : ℕ
  hm : 0 < m
  hK : K = 2 * m
  hk : 0 < k
  hH : H = k * K
  hD : D = 2 * m * H
  hKpos : 0 < K
  hHpos : 0 < H
  hDpos : 0 < D
  hboundary : 2 * m ≤ K
  hHltD : H < D
  htail : failureRatio K ^ k < (1 / 2 : ℝ) ^ (m + 1)
  hlower : (2 : ℝ) / 3 - ε < paperLowerBound m

theorem exists_selectedParameters (ε : ℝ) (hε : 0 < ε) :
    Nonempty (SelectedParameters ε) := by
  obtain ⟨m, hm, hlower⟩ := exists_paperLowerBound_near_two_thirds ε hε
  let K := 2 * m
  have hKpos : 0 < K := by
    dsimp [K]
    omega
  have htargetPos : 0 < (1 / 2 : ℝ) ^ (m + 1) := by positivity
  obtain ⟨k, htail⟩ := exists_pow_failure_lt hKpos htargetPos
  have htargetLt : (1 / 2 : ℝ) ^ (m + 1) < 1 := by
    apply pow_lt_one (by norm_num) (by norm_num)
    omega
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hk0, pow_zero] at htail
    linarith
  let H := k * K
  have hHpos : 0 < H := by
    dsimp [H]
    exact Nat.mul_pos hk hKpos
  let D := 2 * m * H
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hHltD : H < D := by
    have htwo : 2 ≤ 2 * m := by omega
    have hfirst : H < 2 * H := by omega
    have hsecond : 2 * H ≤ 2 * m * H := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_le_mul_right H htwo
    exact hfirst.trans_le hsecond
  exact ⟨{
    m := m
    K := K
    k := k
    H := H
    D := D
    hm := hm
    hK := rfl
    hk := hk
    hH := rfl
    hD := rfl
    hKpos := hKpos
    hHpos := hHpos
    hDpos := hDpos
    hboundary := by simp [K]
    hHltD := hHltD
    htail := htail
    hlower := hlower
  }⟩

namespace SelectedParameters

variable {ε : ℝ}

@[simp] theorem K_eq (p : SelectedParameters ε) : p.K = 2 * p.m := p.hK

@[simp] theorem H_eq (p : SelectedParameters ε) : p.H = p.k * p.K := p.hH

@[simp] theorem D_eq (p : SelectedParameters ε) : p.D = 2 * p.m * p.H := p.hD

theorem two_H_le_D (p : SelectedParameters ε) : 2 * p.H ≤ p.D := by
  rw [p.hD]
  have hm2 : 2 ≤ 2 * p.m := by
    have hm := p.hm
    omega
  exact @Nat.mul_le_mul_right 2 (2 * p.m) p.H hm2

end SelectedParameters

theorem failure_error_absorption {m K k : ℕ} (hm : 0 < m)
    (htail : failureRatio K ^ k < (1 / 2 : ℝ) ^ (m + 1)) :
    (1 + 4 * (m : ℝ)) * failureRatio K ^ k ≤
      3 * (m : ℝ) * (1 / 2 : ℝ) ^ m := by
  let q : ℝ := (1 / 2 : ℝ) ^ m
  have hq : 0 ≤ q := by positivity
  have hcoefPos : 0 < 1 + 4 * (m : ℝ) := by positivity
  have hmul := mul_lt_mul_of_pos_left htail hcoefPos
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcoef : (1 + 4 * (m : ℝ)) * (1 / 2 : ℝ) ≤ 3 * (m : ℝ) := by
    linarith
  calc
    (1 + 4 * (m : ℝ)) * failureRatio K ^ k ≤
        (1 + 4 * (m : ℝ)) * (1 / 2 : ℝ) ^ (m + 1) := hmul.le
    _ = ((1 + 4 * (m : ℝ)) * (1 / 2 : ℝ)) * q := by
      simp only [q, pow_succ]
      ring
    _ ≤ (3 * (m : ℝ)) * q := mul_le_mul_of_nonneg_right hcoef hq
    _ = 3 * (m : ℝ) * (1 / 2 : ℝ) ^ m := rfl

theorem SelectedParameters.failure_error_absorption (p : SelectedParameters ε) :
    (1 + 4 * (p.m : ℝ)) * failureRatio p.K ^ p.k ≤
      3 * (p.m : ℝ) * (1 / 2 : ℝ) ^ p.m :=
  PaperParameterSelection.failure_error_absorption p.hm p.htail

theorem centralDelayFactor_eq {m H D : ℕ} (hm : 0 < m) (hH : 0 < H)
    (hD : D = 2 * m * H) :
    (((D - 2 * H : ℕ) : ℝ) / D) = 1 - 1 / (m : ℝ) := by
  subst D
  have htwo : 2 * H ≤ 2 * m * H := by
    exact @Nat.mul_le_mul_right 2 (2 * m) H (by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  rw [Nat.cast_sub htwo]
  push_cast
  field_simp [hm0, hH0]
  ring

theorem SelectedParameters.centralDelayFactor_eq (p : SelectedParameters ε) :
    (((p.D - 2 * p.H : ℕ) : ℝ) / p.D) = 1 - 1 / (p.m : ℝ) :=
  PaperParameterSelection.centralDelayFactor_eq p.hm p.hHpos p.hD

theorem centralFactor_nonneg {m : ℕ} (hm : 0 < m) :
    0 ≤ 1 - 1 / (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by positivity
  have hone : (1 : ℝ) / m ≤ 1 := (div_le_one hmPos).2 hmR
  linarith

theorem centralFactor_le_one {m : ℕ} (hm : 0 < m) :
    1 - 1 / (m : ℝ) ≤ 1 := by
  have hrecip : 0 ≤ 1 / (m : ℝ) := by positivity
  linarith

theorem paperLowerBound_le_central_estimate {m K k : ℕ} (hm : 0 < m)
    (htail : failureRatio K ^ k < (1 / 2 : ℝ) ^ (m + 1)) :
    paperLowerBound m ≤
      (1 - 1 / (m : ℝ)) *
          (2 * (m : ℝ) / (3 * (m : ℝ) + 1) - failureRatio K ^ k) -
        4 * (m : ℝ) * failureRatio K ^ k := by
  let δ := failureRatio K ^ k
  let a := 1 - 1 / (m : ℝ)
  let M := 2 * (m : ℝ) / (3 * (m : ℝ) + 1)
  have hδ : 0 ≤ δ := pow_nonneg (failureRatio_nonneg K) k
  have ha : a ≤ 1 := centralFactor_le_one hm
  have hscaled : (a + 4 * (m : ℝ)) * δ ≤ (1 + 4 * (m : ℝ)) * δ := by
    exact mul_le_mul_of_nonneg_right (by linarith) hδ
  have habsorb : (1 + 4 * (m : ℝ)) * δ ≤
      3 * (m : ℝ) * (1 / 2 : ℝ) ^ m :=
    failure_error_absorption hm htail
  have herr : (a + 4 * (m : ℝ)) * δ ≤
      3 * (m : ℝ) * (1 / 2 : ℝ) ^ m := hscaled.trans habsorb
  rw [paperLowerBound_eq m hm]
  change a * M - 3 * (m : ℝ) * (1 / 2 : ℝ) ^ m ≤
    a * (M - δ) - 4 * (m : ℝ) * δ
  calc
    a * M - 3 * (m : ℝ) * (1 / 2 : ℝ) ^ m ≤
        a * M - (a + 4 * (m : ℝ)) * δ := sub_le_sub_left herr _
    _ = a * (M - δ) - 4 * (m : ℝ) * δ := by ring

theorem SelectedParameters.paperLowerBound_le_central_estimate
    (p : SelectedParameters ε) :
    paperLowerBound p.m ≤
      (1 - 1 / (p.m : ℝ)) *
          (2 * (p.m : ℝ) / (3 * (p.m : ℝ) + 1) - failureRatio p.K ^ p.k) -
        4 * (p.m : ℝ) * failureRatio p.K ^ p.k :=
  PaperParameterSelection.paperLowerBound_le_central_estimate p.hm p.htail

end PaperParameterSelection
