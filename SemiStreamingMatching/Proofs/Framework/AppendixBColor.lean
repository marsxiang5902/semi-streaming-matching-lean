import SemiStreamingMatching.Proofs.Framework.AppendixBConstruction
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

namespace AppendixBColor

open scoped BigOperators

def badCoordinateValues (p a : ℕ) : Finset (Fin p) :=
  Finset.univ.filter fun z ↦ p ≤ z.val + a

theorem badCoordinateValues_card_le (p a : ℕ) :
    (badCoordinateValues p a).card ≤ a := by
  classical
  let s := badCoordinateValues p a
  let distance : Fin p → ℕ := fun z ↦ p - 1 - z.val
  have hinj : Set.InjOn distance (↑s : Set (Fin p)) := by
    intro z hz w hw heq
    have hzlt := z.isLt
    have hwlt := w.isLt
    apply Fin.ext
    dsimp only [distance] at heq
    omega
  have himageCard : (s.image distance).card = s.card :=
    Finset.card_image_iff.mpr hinj
  have himageSubset : s.image distance ⊆ Finset.range a := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    have hzbad : p ≤ z.val + a := (Finset.mem_filter.mp hz).2
    rw [Finset.mem_range]
    dsimp only [distance]
    omega
  calc
    s.card = (s.image distance).card := himageCard.symm
    _ ≤ (Finset.range a).card := Finset.card_le_card himageSubset
    _ = a := Finset.card_range a

def badAtCoordinate {d p : ℕ} (k : Fin d) (a : ℕ) :
    Finset (AppendixBConstruction.Box d p) :=
  Finset.univ.filter fun u ↦ p ≤ (u k).val + a

theorem badAtCoordinate_card_eq {d p : ℕ} (k : Fin d) (a : ℕ) :
    (badAtCoordinate (p := p) k a).card =
      (badCoordinateValues p a).card * p ^ (d - 1) := by
  classical
  let split := Equiv.funSplitAt k (Fin p)
  let source := badAtCoordinate (p := p) k a
  let target := badCoordinateValues p a ×ˢ
    (Finset.univ : Finset ({j : Fin d // j ≠ k} → Fin p))
  have hcard : source.card = target.card := by
    apply Finset.card_congr (fun u _ ↦ split u)
    · intro u hu
      have hubad := (Finset.mem_filter.mp hu).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [split] using hubad⟩,
          Finset.mem_univ _⟩
    · intro u v _ _ huv
      exact split.injective huv
    · intro pair hpair
      refine ⟨split.symm pair, ?_, split.apply_symm_apply pair⟩
      have hpbad := (Finset.mem_filter.mp (Finset.mem_product.mp hpair).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [split] using hpbad⟩
  rw [hcard, Finset.card_product]
  simp only [target, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  simp

theorem badAtCoordinate_card_le {d p : ℕ} (k : Fin d) (a : ℕ) :
    (badAtCoordinate (p := p) k a).card ≤ a * p ^ (d - 1) := by
  rw [badAtCoordinate_card_eq (p := p)]
  exact Nat.mul_le_mul_right _ (badCoordinateValues_card_le p a)

noncomputable def badFits {d p : ℕ} (S : Finset (Fin d)) (a : ℕ) :
    Finset (AppendixBConstruction.Box d p) := by
  classical
  exact Finset.univ.filter fun u ↦ ¬AppendixBConstruction.Fits S a u

theorem badFits_card_le {d p : ℕ} (S : Finset (Fin d)) (a : ℕ) :
    (badFits (p := p) S a).card ≤ S.card * (a * p ^ (d - 1)) := by
  classical
  have hsubset : badFits (p := p) S a ⊆
      S.biUnion fun k ↦ badAtCoordinate (p := p) k a := by
    intro u hu
    have hnot := (Finset.mem_filter.mp hu).2
    simp only [AppendixBConstruction.Fits] at hnot
    push_neg at hnot
    obtain ⟨k, hkS, hkbad⟩ := hnot
    simp only [Finset.mem_biUnion]
    exact ⟨k, hkS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  calc
    (badFits (p := p) S a).card ≤
        (S.biUnion fun k ↦ badAtCoordinate (p := p) k a).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ k ∈ S, (badAtCoordinate (p := p) k a).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ S, (a * p ^ (d - 1)) := by
      exact Finset.sum_le_sum fun k hk ↦ badAtCoordinate_card_le (p := p) k a
    _ = S.card * (a * p ^ (d - 1)) := by simp

structure BufferedParameters where
  C : ℕ
  B : ℕ
  W : ℕ
  C_pos : 0 < C
  B_pos : 0 < B
  W_pos : 0 < W

namespace BufferedParameters

def P (K : BufferedParameters) : ℕ := K.B + K.W

def Q (K : BufferedParameters) : ℕ := K.C * K.P

theorem P_pos (K : BufferedParameters) : 0 < K.P := by
  simp only [P]
  exact lt_of_lt_of_le K.B_pos (Nat.le_add_right _ _)

theorem Q_pos (K : BufferedParameters) : 0 < K.Q := by
  simp only [Q]
  exact Nat.mul_pos K.C_pos K.P_pos

def color (K : BufferedParameters) (w : ℕ) : Option (Fin K.C) :=
  if w % K.P < K.B then
    some ⟨(w / K.P) % K.C, Nat.mod_lt _ K.C_pos⟩
  else none

theorem color_eq_some_iff (K : BufferedParameters) (w : ℕ) (x : Fin K.C) :
    K.color w = some x ↔
      w % K.P < K.B ∧ (w / K.P) % K.C = x.val := by
  unfold color
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro hfin
      exact ⟨h, congrArg Fin.val hfin⟩
    · intro hval
      exact Fin.ext hval.2
  · simp [h]

theorem exists_block_representation_of_color (K : BufferedParameters)
    {w : ℕ} {x : Fin K.C} (hx : K.color w = some x) :
    ∃ block offset,
      w = K.P * block + offset ∧
      offset < K.B ∧ block % K.C = x.val := by
  rw [K.color_eq_some_iff] at hx
  refine ⟨w / K.P, w % K.P, ?_, hx.1, hx.2⟩
  exact (Nat.div_add_mod w K.P).symm

def cyclicBlocks (K : BufferedParameters) (x y : Fin K.C) : ℕ :=
  K.C - x.val + y.val

theorem cyclicBlocks_pos (K : BufferedParameters) (x y : Fin K.C) :
    0 < K.cyclicBlocks x y := by
  simp only [cyclicBlocks]
  omega

theorem cyclicBlocks_lt_two_mul (K : BufferedParameters) (x y : Fin K.C) :
    K.cyclicBlocks x y < 2 * K.C := by
  simp only [cyclicBlocks]
  omega

private theorem add_cyclicBlocks_mod (K : BufferedParameters)
    (x y : Fin K.C) {block : ℕ} (hblock : block % K.C = x.val) :
    (block + K.cyclicBlocks x y) % K.C = y.val := by
  have hdiv := Nat.div_add_mod block K.C
  rw [hblock] at hdiv
  have hxy : x.val + (K.C - x.val + y.val) = K.C + y.val := by omega
  calc
    (block + K.cyclicBlocks x y) % K.C =
        (block + (K.C - x.val + y.val)) % K.C := by rfl
    _ =
        (K.C * (block / K.C) + x.val +
          (K.C - x.val + y.val)) % K.C :=
      congrArg (fun z ↦ (z + (K.C - x.val + y.val)) % K.C) hdiv.symm
    _ = (K.C * (block / K.C) + (K.C + y.val)) % K.C := by
      rw [Nat.add_assoc, hxy]
    _ = y.val := by
      rw [show K.C * (block / K.C) + (K.C + y.val) =
        K.C * (block / K.C + 1) + y.val by ring]
      exact (Nat.mul_add_mod K.C (block / K.C + 1) y.val).trans
        (Nat.mod_eq_of_lt y.isLt)

theorem color_add_cyclicBlocks (K : BufferedParameters)
    {w : ℕ} {x y : Fin K.C} (hx : K.color w = some x) :
    K.color (w + K.P * K.cyclicBlocks x y) = some y := by
  rw [K.color_eq_some_iff] at hx ⊢
  constructor
  · simpa [Nat.add_mul_mod_self_left] using hx.1
  · rw [Nat.add_mul_div_left w (K.cyclicBlocks x y) K.P_pos]
    exact K.add_cyclicBlocks_mod x y hx.2

theorem separated_of_distinct_colors (K : BufferedParameters)
    {u v : ℕ} {x y : Fin K.C}
    (hu : K.color u = some x) (hv : K.color v = some y) (hxy : x ≠ y) :
    u + K.W < v ∨ v + K.W < u := by
  obtain ⟨i, a, hui, ha, hix⟩ := K.exists_block_representation_of_color hu
  obtain ⟨j, b, hvj, hb, hjy⟩ := K.exists_block_representation_of_color hv
  have hij : i ≠ j := by
    intro hij
    subst j
    apply hxy
    apply Fin.ext
    exact hix.symm.trans hjy
  rcases lt_or_gt_of_ne hij with hij | hji
  · left
    have hblocks : K.P * (i + 1) ≤ K.P * j :=
      Nat.mul_le_mul_left K.P (by omega)
    calc
      u + K.W = K.P * i + a + K.W := by rw [hui]
      _ < K.P * i + K.B + K.W := by omega
      _ = K.P * (i + 1) := by simp only [P, Nat.mul_succ]; omega
      _ ≤ K.P * j := hblocks
      _ ≤ K.P * j + b := Nat.le_add_right _ _
      _ = v := hvj.symm
  · right
    have hblocks : K.P * (j + 1) ≤ K.P * i :=
      Nat.mul_le_mul_left K.P (by omega)
    calc
      v + K.W = K.P * j + b + K.W := by rw [hvj]
      _ < K.P * j + K.B + K.W := by omega
      _ = K.P * (j + 1) := by simp only [P, Nat.mul_succ]; omega
      _ ≤ K.P * i := hblocks
      _ ≤ K.P * i + a := Nat.le_add_right _ _
      _ = u := hui.symm

def colorPoint (K : BufferedParameters) (x : Fin K.C) (z : Fin K.B) : Fin K.Q :=
  ⟨z.val + K.P * x.val, by
    have hzP : z.val < K.P := lt_trans z.isLt (by simp [P, K.W_pos])
    calc
      z.val + K.P * x.val < K.P + K.P * x.val := by omega
      _ = K.P * (x.val + 1) := by ring
      _ ≤ K.P * K.C := Nat.mul_le_mul_left K.P x.isLt
      _ = K.Q := by simp only [Q]; ring⟩

@[simp]
theorem color_colorPoint (K : BufferedParameters) (x : Fin K.C) (z : Fin K.B) :
    K.color (K.colorPoint x z).val = some x := by
  rw [K.color_eq_some_iff]
  have hzP : z.val < K.P := lt_trans z.isLt (by simp [P, K.W_pos])
  constructor
  · simpa [colorPoint, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzP]
  · rw [show (K.colorPoint x z).val = z.val + K.P * x.val by rfl]
    rw [Nat.add_mul_div_left z.val x.val K.P_pos, Nat.div_eq_of_lt hzP,
      zero_add, Nat.mod_eq_of_lt x.isLt]

theorem eq_colorPoint_of_color {K : BufferedParameters} {x : Fin K.C}
    {w : Fin K.Q} (hw : K.color w.val = some x) :
    w = K.colorPoint x ⟨w.val % K.P, (K.color_eq_some_iff w.val x).mp hw |>.1⟩ := by
  apply Fin.ext
  rw [show (K.colorPoint x
      ⟨w.val % K.P, (K.color_eq_some_iff w.val x).mp hw |>.1⟩).val =
      w.val % K.P + K.P * x.val by rfl]
  have hquotLt : w.val / K.P < K.C := by
    rw [Nat.div_lt_iff_lt_mul K.P_pos]
    simpa only [Q, mul_comm] using w.isLt
  have hquot : w.val / K.P = x.val := by
    have hx := (K.color_eq_some_iff w.val x).mp hw |>.2
    rwa [Nat.mod_eq_of_lt hquotLt] at hx
  rw [← hquot]
  exact (Nat.div_add_mod w.val K.P).symm.trans (by ring)

theorem color_class_card_one_period (K : BufferedParameters) (x : Fin K.C) :
    (Finset.univ.filter fun w : Fin K.Q ↦ K.color w.val = some x).card = K.B := by
  classical
  let s := Finset.univ.filter fun w : Fin K.Q ↦ K.color w.val = some x
  let t := (Finset.univ : Finset (Fin K.B))
  have hcard : s.card = t.card := by
    apply Finset.card_congr
      (fun w hw ↦
        ⟨w.val % K.P,
          (K.color_eq_some_iff w.val x).mp (Finset.mem_filter.mp hw).2 |>.1⟩)
    · intro w hw
      exact Finset.mem_univ _
    · intro w₁ w₂ hw₁ hw₂ heq
      have hc₁ := (Finset.mem_filter.mp hw₁).2
      have hc₂ := (Finset.mem_filter.mp hw₂).2
      rw [K.eq_colorPoint_of_color hc₁, K.eq_colorPoint_of_color hc₂]
      congr
    · intro z hz
      refine ⟨K.colorPoint x z, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.color_colorPoint x z⟩
      · apply Fin.ext
        change (z.val + K.P * x.val) % K.P = z.val
        rw [Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (lt_trans z.isLt (by simp [P, K.W_pos]))]
  simpa [s, t] using hcard

theorem color_mod_Q (K : BufferedParameters) (w : ℕ) :
    K.color (w % K.Q) = K.color w := by
  have hPdvdQ : K.P ∣ K.Q := ⟨K.C, by simp only [Q]; ring⟩
  have hoff : w % K.Q % K.P = w % K.P := Nat.mod_mod_of_dvd w hPdvdQ
  have hblock : w % K.Q / K.P = w / K.P % K.C := by
    simpa only [Q] using Nat.mod_mul_left_div_self w K.P K.C
  unfold color
  rw [hoff]
  split_ifs
  · congr 1
    apply Fin.ext
    dsimp only
    rw [hblock, Nat.mod_mod]
  · rfl

theorem color_add_mul_Q (K : BufferedParameters) (w k : ℕ) :
    K.color (w + K.Q * k) = K.color w := by
  calc
    K.color (w + K.Q * k) = K.color ((w + K.Q * k) % K.Q) :=
      (K.color_mod_Q (w + K.Q * k)).symm
    _ = K.color (w % K.Q) := by rw [Nat.add_mul_mod_self_left]
    _ = K.color w := K.color_mod_Q w

def rotatePeriod (K : BufferedParameters) (base : ℕ) (z : Fin K.Q) : Fin K.Q :=
  ⟨(base + z.val) % K.Q, Nat.mod_lt _ K.Q_pos⟩

theorem rotatePeriod_injective (K : BufferedParameters) (base : ℕ) :
    Function.Injective (K.rotatePeriod base) := by
  intro z₁ z₂ heq
  have hadd : K.Q.ModEq (base + z₁.val) (base + z₂.val) := by
    exact congrArg Fin.val heq
  have hbase : K.Q.ModEq base base := Nat.ModEq.refl _
  have hz : K.Q.ModEq z₁.val z₂.val := hbase.add_left_cancel hadd
  exact Fin.ext (hz.eq_of_lt_of_lt z₁.isLt z₂.isLt)

theorem color_class_card_shifted_period (K : BufferedParameters)
    (base : ℕ) (x : Fin K.C) :
    (Finset.univ.filter fun z : Fin K.Q ↦ K.color (base + z.val) = some x).card = K.B := by
  classical
  let s := Finset.univ.filter fun z : Fin K.Q ↦ K.color (base + z.val) = some x
  let t := Finset.univ.filter fun z : Fin K.Q ↦ K.color z.val = some x
  have hinj := K.rotatePeriod_injective base
  have hsurj : Function.Surjective (K.rotatePeriod base) :=
    (Finite.injective_iff_surjective.mp hinj)
  have hcard : s.card = t.card := by
    apply Finset.card_congr (fun z _ ↦ K.rotatePeriod base z)
    · intro z hz
      have hzColor := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [rotatePeriod] using
          (K.color_mod_Q (base + z.val)).trans hzColor⟩
    · intro z₁ z₂ _ _ heq
      exact hinj heq
    · intro w hw
      obtain ⟨z, hz⟩ := hsurj w
      refine ⟨z, ?_, hz⟩
      have hwColor := (Finset.mem_filter.mp hw).2
      have hsource : K.color (base + z.val) = some x := by
        rw [← K.color_mod_Q (base + z.val)]
        have hcolorEq := congrArg (fun q : Fin K.Q ↦ K.color q.val) hz
        exact hcolorEq.trans hwColor
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
  rw [hcard]
  exact K.color_class_card_one_period x

theorem color_class_card_shifted_periods (K : BufferedParameters)
    (cycles base : ℕ) (x : Fin K.C) :
    (Finset.univ.filter fun z : Fin (cycles * K.Q) ↦
      K.color (base + z.val) = some x).card = cycles * K.B := by
  classical
  let s := Finset.univ.filter fun z : Fin (cycles * K.Q) ↦
    K.color (base + z.val) = some x
  let periodClass := Finset.univ.filter fun z : Fin K.Q ↦
    K.color (base + z.val) = some x
  let target := (Finset.univ : Finset (Fin cycles)) ×ˢ periodClass
  have hcard : s.card = target.card := by
    apply Finset.card_congr
      (fun z _ ↦ (finProdFinEquiv : Fin cycles × Fin K.Q ≃
        Fin (cycles * K.Q)).symm z)
    · intro z hz
      let pair := (finProdFinEquiv : Fin cycles × Fin K.Q ≃
        Fin (cycles * K.Q)).symm z
      have hval : z.val = pair.2.val + K.Q * pair.1.val := by
        have happly := congrArg Fin.val
          ((finProdFinEquiv : Fin cycles × Fin K.Q ≃
            Fin (cycles * K.Q)).apply_symm_apply z)
        exact happly.symm
      have hzColor := (Finset.mem_filter.mp hz).2
      have hperiod : K.color (base + pair.2.val) = some x := by
        rw [hval, ← Nat.add_assoc] at hzColor
        exact (K.color_add_mul_Q (base + pair.2.val) pair.1.val).symm.trans hzColor
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hperiod⟩⟩
    · intro z₁ z₂ _ _ heq
      exact (finProdFinEquiv : Fin cycles × Fin K.Q ≃
        Fin (cycles * K.Q)).symm.injective heq
    · intro pair hpair
      refine ⟨(finProdFinEquiv : Fin cycles × Fin K.Q ≃
          Fin (cycles * K.Q)) pair, ?_, by simp⟩
      have hperiod := (Finset.mem_filter.mp (Finset.mem_product.mp hpair).2).2
      have hsource : K.color
          (base + ((finProdFinEquiv : Fin cycles × Fin K.Q ≃
            Fin (cycles * K.Q)) pair).val) = some x := by
        change K.color (base + (pair.2.val + K.Q * pair.1.val)) = some x
        rw [← Nat.add_assoc, K.color_add_mul_Q]
        exact hperiod
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
  rw [hcard, Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_fin, target, periodClass]
  rw [K.color_class_card_shifted_period base x]

theorem color_class_card_of_eq (K : BufferedParameters)
    {p cycles : ℕ} (hp : p = cycles * K.Q) (base : ℕ) (x : Fin K.C) :
    (Finset.univ.filter fun z : Fin p ↦ K.color (base + z.val) = some x).card =
      cycles * K.B := by
  subst p
  exact K.color_class_card_shifted_periods cycles base x

theorem color_class_fintype_card_of_eq (K : BufferedParameters)
    {p cycles : ℕ} (hp : p = cycles * K.Q) (base : ℕ) (x : Fin K.C) :
    Fintype.card {z : Fin p // K.color (base + z.val) = some x} =
      cycles * K.B := by
  rw [Fintype.card_subtype]
  exact K.color_class_card_of_eq hp base x

end BufferedParameters

structure ArithmeticBoxData (C : ℕ) where
  q : ℕ
  m : ℕ
  p : ℕ
  t : ℕ
  C_pos : 0 < C
  m_pos : 0 < m
  p_pos : 0 < p
  t_pos : 0 < t
  delta_small : 40 * C < q
  supports : Fin t → Finset (Fin (m * q))
  support_card : ∀ i, (supports i).card = m
  intersectionCap : ℕ
  intersection_lt_support : intersectionCap < m
  support_intersection : ∀ {i j}, i ≠ j →
    ((supports i) ∩ (supports j)).card ≤ intersectionCap

  intersectionCap_scaled : q * intersectionCap ≤ 4 * m

namespace ArithmeticBoxData

variable {C : ℕ}

def A (D : ArithmeticBoxData C) : ℕ := 10 * C + D.q

def B (D : ArithmeticBoxData C) : ℕ := D.m * D.q

def W (D : ArithmeticBoxData C) : ℕ := 10 * C * D.m

def P (D : ArithmeticBoxData C) : ℕ := D.B + D.W

def Q (D : ArithmeticBoxData C) : ℕ := C * D.P

theorem q_pos (D : ArithmeticBoxData C) : 0 < D.q := by
  have := D.delta_small
  omega

theorem A_pos (D : ArithmeticBoxData C) : 0 < D.A := by
  simp only [A]
  exact lt_of_lt_of_le D.q_pos (Nat.le_add_left _ _)

theorem B_pos (D : ArithmeticBoxData C) : 0 < D.B :=
  Nat.mul_pos D.m_pos D.q_pos

theorem W_pos (D : ArithmeticBoxData C) : 0 < D.W := by
  simp only [W]
  exact Nat.mul_pos (Nat.mul_pos (by omega) D.C_pos) D.m_pos

theorem P_eq_mul_A (D : ArithmeticBoxData C) : D.P = D.m * D.A := by
  simp only [P, B, W, A]
  ring

def buffered (D : ArithmeticBoxData C) : BufferedParameters where
  C := C
  B := D.B
  W := D.W
  C_pos := D.C_pos
  B_pos := D.B_pos
  W_pos := D.W_pos

@[simp]
theorem buffered_P (D : ArithmeticBoxData C) : D.buffered.P = D.P := rfl

@[simp]
theorem buffered_color (D : ArithmeticBoxData C) (w : ℕ) :
    D.buffered.color w =
      if w % D.P < D.B then
        some ⟨(w / D.P) % C, Nat.mod_lt _ D.C_pos⟩
      else none := rfl

def weight {d p : ℕ} (S : Finset (Fin d))
    (u : AppendixBConstruction.Box d p) : ℕ :=
  ∑ k ∈ S, (u k).val

def color (D : ArithmeticBoxData C) (i : Fin D.t)
    (u : AppendixBConstruction.Box (D.m * D.q) D.p) : Option (Fin C) :=
  D.buffered.color (weight (D.supports i) u)

def shift (D : ArithmeticBoxData C) (x y : Fin C) : ℕ :=
  D.buffered.cyclicBlocks x y * D.A

theorem shift_formula (D : ArithmeticBoxData C) (x y : Fin C) :
    D.shift x y = (C - x.val + y.val) * (10 * C + D.q) := rfl

theorem shift_pos (D : ArithmeticBoxData C) (x y : Fin C) :
    0 < D.shift x y :=
  Nat.mul_pos (D.buffered.cyclicBlocks_pos x y) D.A_pos

theorem weight_translate {d p : ℕ} (S T : Finset (Fin d)) (a : ℕ)
    (u : AppendixBConstruction.Box d p)
    (h : AppendixBConstruction.Fits T a u) :
    weight S (AppendixBConstruction.translate T a u h) =
      weight S u + (S ∩ T).card * a := by
  classical
  calc
    weight S (AppendixBConstruction.translate T a u h) =
        ∑ k ∈ S, ((u k).val + if k ∈ T then a else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hT : k ∈ T
      · simp [AppendixBConstruction.translate, hT]
      · simp [AppendixBConstruction.translate, hT]
    _ = (∑ k ∈ S, (u k).val) + (∑ k ∈ S, if k ∈ T then a else 0) := by
      exact Finset.sum_add_distrib
    _ = weight S u + (S ∩ T).card * a := by
      simp only [weight]
      congr 1
      induction S using Finset.induction_on with
      | empty => simp
      | @insert k S hk ih =>
          by_cases hT : k ∈ T <;> simp [hk, hT, ih]

theorem weight_eq_pivot_add {d p : ℕ} (S : Finset (Fin d))
    {k : Fin d} (hk : k ∈ S) (u : AppendixBConstruction.Box d p) :
    weight S u = (u k).val + weight (S.erase k) u := by
  simp only [weight]
  calc
    (∑ j ∈ S, (u j).val) =
        (∑ j ∈ S.erase k, (u j).val) + (u k).val :=
      (Finset.sum_erase_add S (fun j ↦ (u j).val) hk).symm
    _ = (u k).val + ∑ j ∈ S.erase k, (u j).val := Nat.add_comm _ _

noncomputable def pivot (D : ArithmeticBoxData C) (i : Fin D.t) :
    Fin (D.m * D.q) := by
  classical
  have hcard : 0 < (D.supports i).card := by rw [D.support_card]; exact D.m_pos
  exact Classical.choose (Finset.card_pos.mp hcard)

theorem pivot_mem (D : ArithmeticBoxData C) (i : Fin D.t) :
    D.pivot i ∈ D.supports i := by
  classical
  have hcard : 0 < (D.supports i).card := by rw [D.support_card]; exact D.m_pos
  exact Classical.choose_spec (Finset.card_pos.mp hcard)

noncomputable def splitBox (D : ArithmeticBoxData C) (i : Fin D.t) :
    AppendixBConstruction.Box (D.m * D.q) D.p ≃
      Fin D.p × ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) :=
  Equiv.funSplitAt (D.pivot i) (Fin D.p)

noncomputable def assembleBox (D : ArithmeticBoxData C) (i : Fin D.t)
    (z : Fin D.p)
    (rest : {j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) :
    AppendixBConstruction.Box (D.m * D.q) D.p :=
  (D.splitBox i).symm (z, rest)

noncomputable def restWeight (D : ArithmeticBoxData C) (i : Fin D.t)
    (rest : {j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) : ℕ :=
  weight (D.supports i)
    (D.assembleBox i ⟨0, D.p_pos⟩ rest)

theorem weight_assembleBox (D : ArithmeticBoxData C) (i : Fin D.t)
    (z : Fin D.p)
    (rest : {j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) :
    weight (D.supports i) (D.assembleBox i z rest) =
      D.restWeight i rest + z.val := by
  classical
  rw [weight_eq_pivot_add (D.supports i) (D.pivot_mem i), restWeight,
    weight_eq_pivot_add (D.supports i) (D.pivot_mem i)]
  have hpivotZ : (D.assembleBox i z rest (D.pivot i)).val = z.val := by
    simp [assembleBox, splitBox, Equiv.funSplitAt, Equiv.piSplitAt]
  have hpivotZero :
      (D.assembleBox i ⟨0, D.p_pos⟩ rest (D.pivot i)).val = 0 := by
    simp [assembleBox, splitBox, Equiv.funSplitAt, Equiv.piSplitAt]
  have herase : weight ((D.supports i).erase (D.pivot i))
      (D.assembleBox i z rest) =
      weight ((D.supports i).erase (D.pivot i))
        (D.assembleBox i ⟨0, D.p_pos⟩ rest) := by
    unfold weight
    apply Finset.sum_congr rfl
    intro j hj
    have hjne : j ≠ D.pivot i := (Finset.mem_erase.mp hj).1
    simp [assembleBox, splitBox, Equiv.funSplitAt, Equiv.piSplitAt, hjne]
  rw [hpivotZ, hpivotZero, zero_add, herase]
  exact Nat.add_comm _ _

def subtypeProdEquivSigma {A B : Type*} (R : A → B → Prop) :
    {pair : A × B // R pair.1 pair.2} ≃ Σ b : B, {a : A // R a b} where
  toFun pair := ⟨pair.val.2, ⟨pair.val.1, pair.property⟩⟩
  invFun pair := ⟨(pair.2.val, pair.1), pair.2.property⟩
  left_inv pair := rfl
  right_inv pair := by cases pair; rfl

noncomputable def coloredBoxPairEquiv (D : ArithmeticBoxData C)
    (i : Fin D.t) (x : Fin C) :
    {u : AppendixBConstruction.Box (D.m * D.q) D.p // D.color i u = some x} ≃
      {pair : Fin D.p ×
          ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) //
        D.buffered.color (D.restWeight i pair.2 + pair.1.val) = some x} :=
  Equiv.subtypeEquiv (D.splitBox i) fun u ↦ by
    let pair := D.splitBox i u
    have hweight := D.weight_assembleBox i pair.1 pair.2
    have hassemble : D.assembleBox i pair.1 pair.2 = u :=
      (D.splitBox i).symm_apply_apply u
    rw [hassemble] at hweight
    unfold color
    rw [hweight]

noncomputable def coloredBoxEquiv (D : ArithmeticBoxData C)
    (i : Fin D.t) (x : Fin C) :
    {u : AppendixBConstruction.Box (D.m * D.q) D.p // D.color i u = some x} ≃
      Σ rest : ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p),
        {z : Fin D.p //
          D.buffered.color (D.restWeight i rest + z.val) = some x} :=
  (D.coloredBoxPairEquiv i x).trans
    (subtypeProdEquivSigma fun (z : Fin D.p)
      (rest : {j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) ↦
      D.buffered.color (D.restWeight i rest + z.val) = some x)

theorem color_class_card (D : ArithmeticBoxData C)
    {cycles : ℕ} (hp : D.p = cycles * D.Q)
    (i : Fin D.t) (x : Fin C) :
    (Finset.univ.filter fun u : AppendixBConstruction.Box (D.m * D.q) D.p ↦
      D.color i u = some x).card =
      cycles * D.B * D.p ^ (D.m * D.q - 1) := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (D.coloredBoxEquiv i x), Fintype.card_sigma]
  simp_rw [D.buffered.color_class_fintype_card_of_eq hp]
  change (∑ _ : ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p),
      cycles * D.B) = cycles * D.B * D.p ^ (D.m * D.q - 1)
  rw [show (∑ _ : ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p),
      cycles * D.B) =
      Fintype.card ({j : Fin (D.m * D.q) // j ≠ D.pivot i} → Fin D.p) *
        (cycles * D.B) by simp]
  rw [Fintype.card_fun]
  simp
  ring

noncomputable def eligibleSources (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C) :
    Finset (AppendixBConstruction.Box (D.m * D.q) D.p) := by
  classical
  exact Finset.univ.filter fun u ↦
    D.color i u = some x ∧
      AppendixBConstruction.Fits (D.supports i) (D.shift x y) u

theorem eligibleSources_card_lower (D : ArithmeticBoxData C)
    {cycles : ℕ} (hp : D.p = cycles * D.Q)
    (i : Fin D.t) (x y : Fin C) :
    cycles * D.B * D.p ^ (D.m * D.q - 1) -
        D.m * (D.shift x y * D.p ^ (D.m * D.q - 1)) ≤
      (D.eligibleSources i x y).card := by
  classical
  let colorSet := Finset.univ.filter fun u :
    AppendixBConstruction.Box (D.m * D.q) D.p ↦ D.color i u = some x
  let bad := badFits (p := D.p) (D.supports i) (D.shift x y)
  have hsubset : colorSet ⊆ D.eligibleSources i x y ∪ bad := by
    intro u hu
    have hcolor := (Finset.mem_filter.mp hu).2
    by_cases hfit : AppendixBConstruction.Fits (D.supports i) (D.shift x y) u
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor, hfit⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfit⟩)
  have hcolorCard : colorSet.card =
      cycles * D.B * D.p ^ (D.m * D.q - 1) := D.color_class_card hp i x
  have hbad : bad.card ≤
      D.m * (D.shift x y * D.p ^ (D.m * D.q - 1)) := by
    simpa [bad, D.support_card] using
      (badFits_card_le (p := D.p) (D.supports i) (D.shift x y))
  have hunion := Finset.card_le_card hsubset
  have hunionBound := Finset.card_union_le (D.eligibleSources i x y) bad
  rw [hcolorCard] at hunion
  omega

noncomputable def translatedBox (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C)
    (u : AppendixBConstruction.Box (D.m * D.q) D.p) :
    AppendixBConstruction.Box (D.m * D.q) D.p := by
  classical
  exact if h : AppendixBConstruction.Fits (D.supports i) (D.shift x y) u then
    AppendixBConstruction.translate (D.supports i) (D.shift x y) u h
  else u

theorem translate?_eq_some_translatedBox (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C)
    {u : AppendixBConstruction.Box (D.m * D.q) D.p}
    (hfit : AppendixBConstruction.Fits (D.supports i) (D.shift x y) u) :
    AppendixBConstruction.translate? (D.supports i) (D.shift x y) u =
      some (D.translatedBox i x y u) := by
  rw [AppendixBConstruction.translate?_eq_some_iff]
  refine ⟨hfit, ?_⟩
  simp [translatedBox, hfit]

noncomputable def encodedTranslatedEdge (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C)
    (u : AppendixBConstruction.Box (D.m * D.q) D.p) :
    Edge (Fin (Fintype.card
      (AppendixBConstruction.Box (D.m * D.q) D.p)))
      (Fin (Fintype.card
        (AppendixBConstruction.Box (D.m * D.q) D.p))) :=
  ((Fintype.equivFin _ ) u,
    (Fintype.equivFin _) (D.translatedBox i x y u))

theorem encodedTranslatedEdge_injective (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C) :
    Function.Injective (D.encodedTranslatedEdge i x y) := by
  intro u v huv
  apply (Fintype.equivFin
    (AppendixBConstruction.Box (D.m * D.q) D.p)).injective
  exact congrArg Prod.fst huv

theorem support_card_mul_shift (D : ArithmeticBoxData C)
    (i : Fin D.t) (x y : Fin C) :
    (D.supports i).card * D.shift x y =
      D.P * D.buffered.cyclicBlocks x y := by
  rw [D.support_card, D.P_eq_mul_A]
  simp only [shift]
  ring

theorem color_translate_same_support (D : ArithmeticBoxData C)
    {i : Fin D.t} {x y : Fin C}
    {u v : AppendixBConstruction.Box (D.m * D.q) D.p}
    (hu : D.color i u = some x)
    (huv : AppendixBConstruction.translate? (D.supports i) (D.shift x y) u = some v) :
    D.color i v = some y := by
  rw [AppendixBConstruction.translate?_eq_some_iff] at huv
  obtain ⟨hfit, rfl⟩ := huv
  unfold color
  rw [weight_translate, Finset.inter_self, D.support_card_mul_shift]
  exact D.buffered.color_add_cyclicBlocks hu

theorem cross_weight_increment_lt_W (D : ArithmeticBoxData C)
    {i j : Fin D.t} (hij : i ≠ j) (x y : Fin C) :
    ((D.supports i) ∩ (D.supports j)).card * D.shift x y < D.W := by
  let I := ((D.supports i) ∩ (D.supports j)).card
  let K := D.buffered.cyclicBlocks x y
  have hIcap : I ≤ D.intersectionCap := D.support_intersection hij
  have hIq : D.q * I ≤ 4 * D.m := by
    exact le_trans (Nat.mul_le_mul_left D.q hIcap) D.intersectionCap_scaled
  have hK : K < 2 * C := D.buffered.cyclicBlocks_lt_two_mul x y
  have hA : 4 * D.A < 5 * D.q := by
    have hsmall := D.delta_small
    simp only [A]
    omega
  by_cases hIzero : I = 0
  · change I * D.shift x y < D.W
    rw [hIzero]
    simpa using D.W_pos
  have hIpos : 0 < I := Nat.pos_of_ne_zero hIzero
  have htwoCpos : 0 < 2 * C := Nat.mul_pos (by omega) D.C_pos
  have hIApos : 0 < I * D.A := Nat.mul_pos hIpos D.A_pos
  have h₁ : I * K * D.A < I * (2 * C) * D.A := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left hK hIpos) D.A_pos
  have h₂raw : (I * (2 * C)) * (4 * D.A) <
      (I * (2 * C)) * (5 * D.q) := by
    exact Nat.mul_lt_mul_of_pos_left hA (Nat.mul_pos hIpos htwoCpos)
  have h₃raw : (10 * C) * (D.q * I) ≤ (10 * C) * (4 * D.m) :=
    Nat.mul_le_mul_left (10 * C) hIq
  have h₁four : 4 * (I * K * D.A) < 4 * (I * (2 * C) * D.A) :=
    Nat.mul_lt_mul_of_pos_left h₁ (by omega)
  have h₂ : 4 * (I * (2 * C) * D.A) <
      5 * (I * (2 * C) * D.q) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h₂raw
  have h₃ : 5 * (I * (2 * C) * D.q) ≤ 4 * (10 * C * D.m) := by
    calc
      5 * (I * (2 * C) * D.q) = (10 * C) * (D.q * I) := by ring
      _ ≤ (10 * C) * (4 * D.m) := h₃raw
      _ = 4 * (10 * C * D.m) := by ring
  have hfour : 4 * (I * K * D.A) < 4 * (10 * C * D.m) :=
    lt_of_lt_of_le (lt_trans h₁four h₂) h₃
  have hresult : I * K * D.A < 10 * C * D.m :=
    Nat.lt_of_mul_lt_mul_left hfour
  simpa only [I, K, shift, W, mul_assoc] using hresult

theorem cross_color (D : ArithmeticBoxData C)
    {i j : Fin D.t} {x y a b : Fin C}
    {u v : AppendixBConstruction.Box (D.m * D.q) D.p}
    (hij : i ≠ j)
    (hua : D.color i u = some a)
    (hvb : D.color i v = some b)
    (huv : AppendixBConstruction.translate? (D.supports j) (D.shift x y) u = some v) :
    a = b := by
  rw [AppendixBConstruction.translate?_eq_some_iff] at huv
  obtain ⟨hfit, rfl⟩ := huv
  by_contra hab
  have hsep := D.buffered.separated_of_distinct_colors hua hvb hab
  have hweight := weight_translate (D.supports i) (D.supports j)
    (D.shift x y) u hfit
  have hsmall := D.cross_weight_increment_lt_W hij x y
  unfold color at hua hvb
  change weight (D.supports i) u + D.W <
      weight (D.supports i)
        (AppendixBConstruction.translate (D.supports j) (D.shift x y) u hfit) ∨
    weight (D.supports i)
        (AppendixBConstruction.translate (D.supports j) (D.shift x y) u hfit) + D.W <
      weight (D.supports i) u at hsep
  rcases hsep with hforward | hbackward
  · rw [hweight] at hforward
    omega
  · rw [hweight] at hbackward
    exact (Nat.not_lt_of_ge
      (le_trans
        (Nat.le_add_right (weight (D.supports i) u)
          ((D.supports i ∩ D.supports j).card * D.shift x y))
        (Nat.le_add_right
          (weight (D.supports i) u +
            (D.supports i ∩ D.supports j).card * D.shift x y) D.W))) hbackward

theorem rawFiber_card_lower (D : ArithmeticBoxData C)
    {cycles : ℕ} (hp : D.p = cycles * D.Q)
    (i : Fin D.t) (x y : Fin C) :
    cycles * D.B * D.p ^ (D.m * D.q - 1) -
        D.m * (D.shift x y * D.p ^ (D.m * D.q - 1)) ≤
      (Finset.univ.filter fun e :
        Edge (Fin (Fintype.card
          (AppendixBConstruction.Box (D.m * D.q) D.p)))
          (Fin (Fintype.card
            (AppendixBConstruction.Box (D.m * D.q) D.p))) ↦
        D.color i ((Fintype.equivFin
          (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.1) = some x ∧
        D.color i ((Fintype.equivFin
          (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.2) = some y ∧
        AppendixBConstruction.translate? (D.supports i) (D.shift x y)
          ((Fintype.equivFin
            (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.1) =
          some ((Fintype.equivFin
            (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.2)).card := by
  classical
  let imageEdges := (D.eligibleSources i x y).image
    (D.encodedTranslatedEdge i x y)
  let target := Finset.univ.filter fun e :
    Edge (Fin (Fintype.card
      (AppendixBConstruction.Box (D.m * D.q) D.p)))
      (Fin (Fintype.card
        (AppendixBConstruction.Box (D.m * D.q) D.p))) ↦
    D.color i ((Fintype.equivFin
      (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.1) = some x ∧
    D.color i ((Fintype.equivFin
      (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.2) = some y ∧
    AppendixBConstruction.translate? (D.supports i) (D.shift x y)
      ((Fintype.equivFin
        (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.1) =
      some ((Fintype.equivFin
        (AppendixBConstruction.Box (D.m * D.q) D.p)).symm e.2)
  have himageCard : imageEdges.card = (D.eligibleSources i x y).card := by
    exact Finset.card_image_of_injective _ (D.encodedTranslatedEdge_injective i x y)
  have himageSubset : imageEdges ⊆ target := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have helig := (Finset.mem_filter.mp hu).2
    have htrans := D.translate?_eq_some_translatedBox i x y helig.2
    have hy := D.color_translate_same_support helig.1 htrans
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [encodedTranslatedEdge] using And.intro helig.1 (And.intro hy htrans)⟩
  have htarget : imageEdges.card ≤ target.card := Finset.card_le_card himageSubset
  have heligLower := D.eligibleSources_card_lower hp i x y
  change _ ≤ target.card
  exact le_trans heligLower (himageCard ▸ htarget)

def maxShift (D : ArithmeticBoxData C) : ℕ :=
  (2 * C - 1) * D.A

theorem shift_le_maxShift (D : ArithmeticBoxData C) (x y : Fin C) :
    D.shift x y ≤ D.maxShift := by
  have hklt := D.buffered.cyclicBlocks_lt_two_mul x y
  change D.buffered.cyclicBlocks x y < 2 * C at hklt
  have hkle : D.buffered.cyclicBlocks x y ≤ 2 * C - 1 := by omega
  exact Nat.mul_le_mul_right D.A hkle

def totalColorCount (D : ArithmeticBoxData C) (cycles : ℕ) : ℕ :=
  cycles * D.B * D.p ^ (D.m * D.q - 1)

def maxBoundaryLoss (D : ArithmeticBoxData C) : ℕ :=
  D.m * (D.maxShift * D.p ^ (D.m * D.q - 1))

def commonMatchingSize (D : ArithmeticBoxData C) (cycles : ℕ) : ℕ :=
  D.totalColorCount cycles - D.maxBoundaryLoss

theorem actualBoundaryLoss_le_max (D : ArithmeticBoxData C) (x y : Fin C) :
    D.m * (D.shift x y * D.p ^ (D.m * D.q - 1)) ≤ D.maxBoundaryLoss := by
  unfold maxBoundaryLoss
  exact Nat.mul_le_mul_left D.m
    (Nat.mul_le_mul_right (D.p ^ (D.m * D.q - 1)) (D.shift_le_maxShift x y))

theorem maxBoundaryLoss_lt_totalColorCount_of_coeff
    (D : ArithmeticBoxData C) (cycles : ℕ)
    (hcoeff : D.m * D.maxShift < cycles * D.B) :
    D.maxBoundaryLoss < D.totalColorCount cycles := by
  have hpow : 0 < D.p ^ (D.m * D.q - 1) := Nat.pow_pos D.p_pos
  have hmul := Nat.mul_lt_mul_of_pos_right hcoeff hpow
  simpa only [maxBoundaryLoss, totalColorCount, mul_assoc] using hmul

def densityCycles (D : ArithmeticBoxData C) : ℕ :=
  D.m * D.maxShift + 1

theorem densityCycles_coeff (D : ArithmeticBoxData C) :
    D.m * D.maxShift < D.densityCycles * D.B := by
  have hBone : 1 ≤ D.B := D.B_pos
  calc
    D.m * D.maxShift < D.m * D.maxShift + 1 := Nat.lt_succ_self _
    _ = D.densityCycles := rfl
    _ = D.densityCycles * 1 := by simp
    _ ≤ D.densityCycles * D.B := Nat.mul_le_mul_left _ hBone

theorem densityCycles_dense (D : ArithmeticBoxData C) :
    D.maxBoundaryLoss < D.totalColorCount D.densityCycles :=
  D.maxBoundaryLoss_lt_totalColorCount_of_coeff D.densityCycles D.densityCycles_coeff

noncomputable def toBoxConstructionData (D : ArithmeticBoxData C)
    (cycles : ℕ) (hp : D.p = cycles * D.Q)
    (hdense : D.maxBoundaryLoss < D.totalColorCount cycles) :
    AppendixBConstruction.BoxConstructionData C where
  d := D.m * D.q
  p := D.p
  r := D.commonMatchingSize cycles
  t := D.t
  supportWeight := D.m
  intersectionCap := D.intersectionCap
  C_pos := D.C_pos
  p_pos := D.p_pos
  r_pos := Nat.sub_pos_of_lt hdense
  t_pos := D.t_pos
  supports := D.supports
  support_card := D.support_card
  intersection_lt_support := D.intersection_lt_support
  support_intersection := D.support_intersection
  color := D.color
  shift := D.shift
  shift_pos := D.shift_pos
  cross_color := by
    intro i j x y a b u v hij hua hvb huv
    exact D.cross_color hij hua hvb huv
  fiber_card := by
    intro i x y
    have hraw := D.rawFiber_card_lower hp i x y
    have hloss := D.actualBoundaryLoss_le_max x y
    have hsub := Nat.sub_le_sub_left hloss (D.totalColorCount cycles)
    exact le_trans hsub hraw

noncomputable def toAppendixBFiniteData (D : ArithmeticBoxData C)
    (cycles : ℕ) (hp : D.p = cycles * D.Q)
    (hdense : D.maxBoundaryLoss < D.totalColorCount cycles) :
    AppendixBFiniteData C :=
  (D.toBoxConstructionData cycles hp hdense).toAppendixBFiniteData

end ArithmeticBoxData

end AppendixBColor

end ERSFamily

end Formal.Streaming
