import SemiStreamingMatching.Proofs.Framework.AppendixBColor
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Formal.Streaming

namespace ERSFamily

namespace AppendixBSupports

open scoped BigOperators

variable (q s : ℕ)

abbrev Vec := Fin (s + 1) → ZMod q

abbrev Coeff := Fin (s + 1) → Fin (s + 1) → ZMod q

abbrev Point := Vec q s × Vec q s

def m : ℕ := q ^ (2 * (s + 1))

def t : ℕ := q ^ ((s + 1) * (s + 1))

def intersectionCap : ℕ := 2 * q ^ (2 * s + 1)

@[simp]
theorem card_vec [NeZero q] : Fintype.card (Vec q s) = q ^ (s + 1) := by
  simp [Vec, ZMod.card]

@[simp]
theorem card_point [NeZero q] : Fintype.card (Point q s) = m q s := by
  simp only [Point, Fintype.card_prod, card_vec, m]
  rw [← pow_add]
  congr 1
  omega

@[simp]
theorem card_coeff [NeZero q] : Fintype.card (Coeff q s) = t q s := by
  simp only [Coeff, Fintype.card_fun, Fintype.card_fin, ZMod.card, t]
  rw [pow_mul]

abbrev ZeroAt (i : Fin (s + 1)) := {x : Vec q s // x i = 0}

def vecEquivCoordZero [NeZero q] (i : Fin (s + 1)) :
    Vec q s ≃ ZMod q × ZeroAt q s i where
  toFun x := (x i, ⟨Function.update x i 0, by simp⟩)
  invFun z := Function.update z.2.1 i z.1
  left_inv x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_noteq hji]
  right_inv z := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [z.2.2]
      · simp [Function.update_noteq hji]

theorem card_vec_eq_card_mul_zeroAt [NeZero q] (i : Fin (s + 1)) :
    Fintype.card (Vec q s) = q * Fintype.card (ZeroAt q s i) := by
  rw [Fintype.card_congr (vecEquivCoordZero q s i), Fintype.card_prod, ZMod.card]

private theorem zeroAt_injective_on_affineFiber [Fact (Nat.Prime q)]
    (i : Fin (s + 1)) (c : Vec q s) (b : ZMod q) (hi : c i ≠ 0) :
    Function.Injective
      (fun x : {x : Vec q s // (∑ j, c j * x j) + b = 0} ↦
        (⟨Function.update x.1 i 0, by simp⟩ : ZeroAt q s i)) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    have hupd : Function.update x.1 i 0 = Function.update y.1 i 0 :=
      congrArg Subtype.val hxy
    have hrest :
        ∑ k ∈ (Finset.univ.erase i), c k * x.1 k =
          ∑ k ∈ (Finset.univ.erase i), c k * y.1 k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      have := congrFun hupd k
      simp only [Function.update_noteq hki] at this
      rw [this]
    have hsum : (∑ k, c k * x.1 k) = ∑ k, c k * y.1 k := by
      apply add_right_cancel (b := b)
      exact x.2.trans y.2.symm
    have hsplitX := Finset.sum_erase_add (Finset.univ) (fun k ↦ c k * x.1 k)
      (Finset.mem_univ i)
    have hsplitY := Finset.sum_erase_add (Finset.univ) (fun k ↦ c k * y.1 k)
      (Finset.mem_univ i)
    have hterm : c i * x.1 i = c i * y.1 i := by
      rw [← hsplitX, ← hsplitY] at hsum
      rw [hrest] at hsum
      exact add_left_cancel hsum
    exact (mul_left_cancel₀ hi hterm)
  · have hupd := congrArg Subtype.val hxy
    have := congrFun hupd j
    simpa [Function.update_noteq hji] using this

theorem affineFiber_card_scaled [Fact (Nat.Prime q)]
    (i : Fin (s + 1)) (c : Vec q s) (b : ZMod q) (hi : c i ≠ 0) :
    q * (Finset.univ.filter fun x : Vec q s ↦ (∑ j, c j * x j) + b = 0).card ≤
      Fintype.card (Vec q s) := by
  let S := {x : Vec q s // (∑ j, c j * x j) + b = 0}
  have hinj : Function.Injective
      (fun x : S ↦
        (⟨Function.update x.1 i 0, by simp⟩ : ZeroAt q s i)) :=
    zeroAt_injective_on_affineFiber q s i c b hi
  have hcard : Fintype.card S ≤ Fintype.card (ZeroAt q s i) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_subtype] at hcard
  rw [card_vec_eq_card_mul_zeroAt q s i]
  exact Nat.mul_le_mul_left q (by simpa [S] using hcard)

def eval (A : Coeff q s) (z : Point q s) : ZMod q :=
  ∑ i, ∑ j, A i j * z.1 i * z.2 j

theorem eval_sub [NeZero q] (A B : Coeff q s) (z : Point q s) :
    eval q s (A - B) z = eval q s A z - eval q s B z := by
  simp only [eval, Pi.sub_apply, sub_mul]
  simp_rw [Finset.sum_sub_distrib]

theorem bilinear_zero_card_scaled [Fact (Nat.Prime q)]
    (A : Coeff q s) (hA : A ≠ 0) :
    q * (Finset.univ.filter fun z : Point q s ↦ eval q s A z = 0).card ≤
      2 * m q s := by
  classical
  haveI : NeZero q := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hA
    funext i j
    exact h i j
  let V := Vec q s
  let badY : Finset V := Finset.univ.filter fun y ↦ (∑ k, A i k * y k) = 0
  let fiber (y : V) : Finset V :=
    Finset.univ.filter fun x ↦ (∑ a, (∑ b, A a b * y b) * x a) = 0
  have hbad : q * badY.card ≤ Fintype.card V := by
    simpa [badY, V, add_zero] using
      (affineFiber_card_scaled q s j (fun k ↦ A i k) 0 hij)
  have hfiber (y : V) (hy : y ∉ badY) :
      q * (fiber y).card ≤ Fintype.card V := by
    have hcoeff : (∑ b, A i b * y b) ≠ 0 := by
      simpa [badY] using hy
    simpa [fiber, V, add_zero] using
      (affineFiber_card_scaled q s i (fun a ↦ ∑ b, A a b * y b) 0 hcoeff)
  have heval (x y : V) :
      eval q s A (x, y) = ∑ a, (∑ b, A a b * y b) * x a := by
    unfold eval
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hzero_eq :
      (Finset.univ.filter fun z : Point q s ↦ eval q s A z = 0).card =
        ∑ y : V, (fiber y).card := by
    let Z := Finset.univ.filter fun z : Point q s ↦ eval q s A z = 0
    calc
      Z.card = ∑ y ∈ (Finset.univ : Finset V),
          (Z.filter fun z ↦ z.2 = y).card :=
        Finset.card_eq_sum_card_fiberwise (f := fun z : Point q s ↦ z.2)
          (s := Z) (t := Finset.univ) (by simp)
      _ = ∑ y : V, (fiber y).card := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.card_congr (fun z hz ↦ z.1)
        · intro z hz
          simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hz with ⟨hz0, hzy⟩
          subst y
          simpa [heval] using hz0
        · intro a b ha hb hab
          apply Prod.ext hab
          exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        · intro x hx
          refine ⟨(x, y), ?_, rfl⟩
          simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · simpa [fiber, heval] using hx
          · trivial
  rw [hzero_eq]
  rw [Finset.mul_sum]
  calc
    ∑ y : V, q * (fiber y).card =
        (∑ y ∈ badY, q * (fiber y).card) +
          ∑ y ∈ (Finset.univ.filter fun y : V ↦ y ∉ badY),
            q * (fiber y).card := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset V))
        (p := fun y ↦ y ∈ badY) (f := fun y ↦ q * (fiber y).card)]
      simp
    _ ≤ badY.card * (q * Fintype.card V) +
          (Finset.univ.filter fun y : V ↦ y ∉ badY).card * Fintype.card V := by
      apply Nat.add_le_add
      · simpa [nsmul_eq_mul, mul_comm] using
          badY.sum_le_card_nsmul (fun y ↦ q * (fiber y).card)
            (q * Fintype.card V)
            (fun y _ ↦ Nat.mul_le_mul_left q (Finset.card_le_univ (fiber y)))
      · simpa [nsmul_eq_mul, mul_comm] using
          (Finset.univ.filter fun y : V ↦ y ∉ badY).sum_le_card_nsmul
            (fun y ↦ q * (fiber y).card) (Fintype.card V)
            (fun y hy ↦ hfiber y (by simpa using hy))
    _ ≤ Fintype.card V * Fintype.card V +
          Fintype.card V * Fintype.card V := by
      apply Nat.add_le_add
      · calc
          badY.card * (q * Fintype.card V) =
              (q * badY.card) * Fintype.card V := by ring
          _ ≤ Fintype.card V * Fintype.card V :=
            Nat.mul_le_mul_right (Fintype.card V) hbad
      · exact Nat.mul_le_mul_right (Fintype.card V)
          (Finset.card_le_univ (Finset.univ.filter fun y : V ↦ y ∉ badY))
    _ = 2 * m q s := by
      have hVm : Fintype.card V * Fintype.card V = m q s := by
        simpa [V, Point] using card_point q s
      omega

def graphSupport {X F : Type*} [Fintype X] [DecidableEq X] [DecidableEq F]
    (w : X → F) : Finset (X × F) :=
  Finset.univ.image fun x ↦ (x, w x)

@[simp]
theorem mem_graphSupport_iff {X F : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq F] (w : X → F) (z : X × F) :
    z ∈ graphSupport w ↔ z.2 = w z.1 := by
  constructor
  · intro hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
    rfl
  · intro hz
    exact Finset.mem_image.mpr ⟨z.1, Finset.mem_univ _, Prod.ext rfl hz.symm⟩

@[simp]
theorem graphSupport_card {X F : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq F] (w : X → F) :
    (graphSupport w).card = Fintype.card X := by
  rw [graphSupport, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    exact congrArg Prod.fst hxy

theorem graphSupport_inter_card {X F : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq F] (u v : X → F) :
    (graphSupport u ∩ graphSupport v).card =
      (Finset.univ.filter fun x ↦ u x = v x).card := by
  classical
  apply Finset.card_congr (fun z _ ↦ z.1)
  · intro z hz
    rw [Finset.mem_inter] at hz
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (mem_graphSupport_iff u z).mp hz.1 |>.symm.trans
        ((mem_graphSupport_iff v z).mp hz.2)⟩
  · intro a b ha hb hab
    apply Prod.ext hab
    have hau := (mem_graphSupport_iff u a).mp (Finset.mem_inter.mp ha).1
    have hbu := (mem_graphSupport_iff u b).mp (Finset.mem_inter.mp hb).1
    rw [hab] at hau
    exact hau.trans hbu.symm
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨(x, u x), ?_, rfl⟩
    rw [Finset.mem_inter]
    constructor
    · simp
    · rw [mem_graphSupport_iff, hx.2]

noncomputable def coeffEquivFin [NeZero q] : Coeff q s ≃ Fin (t q s) :=
  (Fintype.equivFin (Coeff q s)).trans (finCongr (card_coeff q s))

noncomputable def coordinateEquivFin [NeZero q] :
    Point q s × ZMod q ≃ Fin (m q s * q) :=
  (Fintype.equivFin (Point q s × ZMod q)).trans (finCongr (by
    simp [card_point q s, ZMod.card]))

noncomputable def word [NeZero q] (i : Fin (t q s)) : Point q s → ZMod q :=
  eval q s ((coeffEquivFin q s).symm i)

noncomputable def supports [NeZero q] (i : Fin (t q s)) :
    Finset (Fin (m q s * q)) :=
  (graphSupport (word q s i)).map (coordinateEquivFin q s).toEmbedding

@[simp]
theorem supports_card [NeZero q] (i : Fin (t q s)) :
    (supports q s i).card = m q s := by
  rw [supports, Finset.card_map, graphSupport_card]
  exact card_point q s

theorem q_mul_intersectionCap [Fact (Nat.Prime q)] :
    q * intersectionCap q s = 2 * m q s := by
  simp only [intersectionCap, m]
  rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega, pow_succ]
  ring

theorem supports_intersection [Fact (Nat.Prime q)] {i j : Fin (t q s)}
    (hij : i ≠ j) :
    ((supports q s i) ∩ (supports q s j)).card ≤ intersectionCap q s := by
  classical
  haveI : NeZero q := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
  let A : Coeff q s := (coeffEquivFin q s).symm i
  let B : Coeff q s := (coeffEquivFin q s).symm j
  have hAB : A - B ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hij
    exact (coeffEquivFin q s).symm.injective h
  have hscaled := bilinear_zero_card_scaled q s (A - B) hAB
  have hinter :
      ((supports q s i) ∩ (supports q s j)).card =
        (Finset.univ.filter fun z : Point q s ↦ eval q s (A - B) z = 0).card := by
    rw [supports, supports, ← Finset.map_inter, Finset.card_map,
      graphSupport_inter_card]
    apply Finset.card_congr (fun z _ ↦ z)
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      rw [eval_sub, sub_eq_zero]
      exact hz.2
    · intro a b _ _ hab
      exact hab
    · intro z hz
      refine ⟨z, ?_, rfl⟩
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      rw [eval_sub, sub_eq_zero] at hz
      exact hz.2
  rw [hinter]
  apply Nat.le_of_mul_le_mul_left _ (Fact.out : Nat.Prime q).pos
  calc
    q * (Finset.univ.filter fun z : Point q s ↦ eval q s (A - B) z = 0).card
        ≤ 2 * m q s := hscaled
    _ = q * intersectionCap q s := (q_mul_intersectionCap q s).symm

theorem m_pos [Fact (Nat.Prime q)] : 0 < m q s := by
  exact pow_pos (Fact.out : Nat.Prime q).pos _

theorem t_pos [Fact (Nat.Prime q)] : 0 < t q s := by
  exact pow_pos (Fact.out : Nat.Prime q).pos _

theorem intersectionCap_lt_m [Fact (Nat.Prime q)]
    (hq : 2 < q) : intersectionCap q s < m q s := by
  let a := q ^ (2 * s + 1)
  have ha : 0 < a := pow_pos (Fact.out : Nat.Prime q).pos _
  calc
    intersectionCap q s = 2 * a := rfl
    _ < q * a := Nat.mul_lt_mul_of_pos_right hq ha
    _ = m q s := by
      simp only [a, m]
      rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega, pow_succ]
      ring

noncomputable def toArithmeticBoxData (C q s p : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hp : 0 < p) (hsmall : 40 * C < q) :
    AppendixBColor.ArithmeticBoxData C where
  q := q
  m := m q s
  p := p
  t := t q s
  C_pos := hC
  m_pos := m_pos q s
  p_pos := hp
  t_pos := t_pos q s
  delta_small := hsmall
  supports := supports q s
  support_card := supports_card q s
  intersectionCap := intersectionCap q s
  intersection_lt_support := intersectionCap_lt_m q s (by omega)
  support_intersection := fun hij ↦ supports_intersection q s hij
  intersectionCap_scaled := by
    rw [q_mul_intersectionCap q s]
    omega

theorem exists_prime_alphabet (C : ℕ) :
    ∃ q, 40 * C < q ∧ Nat.Prime q := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (40 * C + 1)
  exact ⟨q, by omega, hprime⟩

def d : ℕ := m q s * q

def boxSide : ℕ := (d q s) ^ 2

def boxVertexCount : ℕ := (boxSide q s) ^ (d q s)

def augmentedBoxSize (P : ℕ) : ℕ := 2 * (boxVertexCount q s) ^ P

theorem d_eq_pow : d q s = q ^ (2 * s + 3) := by
  simp only [d, m]
  rw [show 2 * s + 3 = 2 * (s + 1) + 1 by omega, pow_succ]

theorem nat_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      calc
        n + 2 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 (nat_le_two_pow (n + 1))
        _ = 2 ^ (n + 2) := by rw [pow_succ]; ring

theorem d_le_two_pow (hq : 2 ≤ q) :
    d q s ≤ 2 ^ (q * (2 * s + 3)) := by
  rw [d_eq_pow]
  calc
    q ^ (2 * s + 3) ≤ (2 ^ q) ^ (2 * s + 3) :=
      Nat.pow_le_pow_left (nat_le_two_pow q) _
    _ = 2 ^ (q * (2 * s + 3)) := by rw [pow_mul]

theorem log_augmentedBoxSize_succ_le (hq : 2 ≤ q) (P : ℕ) :
    Nat.log 2 (augmentedBoxSize q s P) + 1 ≤
      2 ^ (P + 3 * q * (2 * s + 3) + 2) := by
  let dd := d q s
  let pp := boxSide q s
  let E := 1 + pp * dd * P
  have hdd : dd ≤ 2 ^ (q * (2 * s + 3)) := d_le_two_pow q s hq
  have hpp : pp = dd ^ 2 := rfl
  have hbase : pp ≤ 2 ^ pp := nat_le_two_pow pp
  have haug_le : augmentedBoxSize q s P ≤ 2 ^ E := by
    calc
      augmentedBoxSize q s P = 2 * pp ^ (dd * P) := by
        simp only [augmentedBoxSize, boxVertexCount]
        rw [pow_mul]
      _ ≤ 2 * (2 ^ pp) ^ (dd * P) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase _)
      _ = 2 ^ E := by
        simp only [E]
        rw [← pow_mul, show 1 + pp * dd * P = 1 + pp * (dd * P) by ring,
          pow_add]
        norm_num
  have haug_pos : 0 < augmentedBoxSize q s P := by
    have hqpos : 0 < q := by omega
    unfold augmentedBoxSize boxVertexCount boxSide d m
    positivity
  have hlog : Nat.log 2 (augmentedBoxSize q s P) + 1 ≤ E + 1 := by
    have hstrict : augmentedBoxSize q s P < 2 ^ (E + 1) :=
      lt_of_le_of_lt haug_le (Nat.pow_lt_pow_succ (by omega))
    have := Nat.log_lt_of_lt_pow haug_pos.ne' hstrict
    omega
  have hcube : pp * dd = dd ^ 3 := by
    rw [hpp]
    ring
  let D := q * (2 * s + 3)
  have hcubeBound : dd ^ 3 ≤ 2 ^ (3 * D) := by
    calc
      dd ^ 3 ≤ (2 ^ D) ^ 3 := Nat.pow_le_pow_left (by simpa [D] using hdd) _
      _ = 2 ^ (D * 3) := (pow_mul 2 D 3).symm
      _ = 2 ^ (3 * D) := by ring
  have hprod : P * dd ^ 3 ≤ 2 ^ (P + 3 * D) := by
    calc
      P * dd ^ 3 ≤ 2 ^ P * 2 ^ (3 * D) :=
        Nat.mul_le_mul (nat_le_two_pow P) hcubeBound
      _ = 2 ^ (P + 3 * D) := (pow_add 2 P (3 * D)).symm
  have htwo : 2 ≤ 2 ^ (P + 3 * D + 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (P + 3 * D + 1) :=
        Nat.pow_le_pow_right (by omega : 0 < 2)
          (Nat.succ_le_succ (Nat.zero_le (P + 3 * D)))
  have hprod' : P * dd ^ 3 ≤ 2 ^ (P + 3 * D + 1) :=
    le_trans hprod (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ _))
  calc
    Nat.log 2 (augmentedBoxSize q s P) + 1 ≤ E + 1 := hlog
    _ = 2 + P * dd ^ 3 := by simp only [E, hcube]; ring
    _ ≤ 2 ^ (P + 3 * D + 1) + 2 ^ (P + 3 * D + 1) :=
      Nat.add_le_add htwo hprod'
    _ = 2 ^ (P + 3 * q * (2 * s + 3) + 2) := by
      simp only [D]
      rw [show P + 3 * q * (2 * s + 3) + 2 =
        (P + 3 * (q * (2 * s + 3)) + 1) + 1 by ring, pow_succ]
      ring

theorem multiplicityGrowth (hq : 2 ≤ q) (P : ℕ) :
    DominatesPolylogAlong
      (fun s ↦ augmentedBoxSize q s P)
      (fun s ↦ t q s) := by
  intro c k
  let A := 6 * q * k
  let B := c + (P + 9 * q + 2) * k
  refine ⟨A + B, fun s hs ↦ ?_⟩
  let L := P + 3 * q * (2 * s + 3) + 2
  have hlog : Nat.log 2 (augmentedBoxSize q s P) + 1 ≤ 2 ^ L := by
    simpa [L] using log_augmentedBoxSize_succ_le q s hq P
  have hA : A ≤ s := le_trans (Nat.le_add_right A B) hs
  have hB : B ≤ s := le_trans (Nat.le_add_left B A) hs
  have hlinear : 6 * q * k * s ≤ s * s := by
    exact Nat.mul_le_mul_right s hA
  have hexp : c + L * k ≤ (s + 1) * (s + 1) := by
    calc
      c + L * k = 6 * q * k * s + B := by simp only [L, B]; ring
      _ ≤ s * s + s := Nat.add_le_add hlinear hB
      _ ≤ (s + 1) * (s + 1) := by nlinarith
  calc
    c * (Nat.log 2 (augmentedBoxSize q s P) + 1) ^ k ≤
        2 ^ c * (2 ^ L) ^ k :=
      Nat.mul_le_mul (nat_le_two_pow c) (Nat.pow_le_pow_left hlog k)
    _ = 2 ^ (c + L * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((s + 1) * (s + 1)) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ q ^ ((s + 1) * (s + 1)) := Nat.pow_le_pow_left hq _
    _ = t q s := rfl

theorem index_le_d (hq : 2 ≤ q) : s ≤ d q s := by
  calc
    s ≤ 2 ^ s := nat_le_two_pow s
    _ ≤ q ^ s := Nat.pow_le_pow_left hq s
    _ ≤ q ^ (2 * s + 3) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    _ = d q s := (d_eq_pow q s).symm

theorem boxVertexCountSizesGrow (hq : 2 ≤ q) :
    SizesTendToInfinity (fun s ↦ boxVertexCount q s) := by
  intro N
  refine ⟨N, fun s hs ↦ ?_⟩
  have hdpos : 0 < d q s := by
    rw [d_eq_pow]
    positivity
  have hindex : s ≤ d q s := index_le_d q s hq
  have hdleSide : d q s ≤ boxSide q s := by
    simp only [boxSide]
    calc
      d q s = (d q s) ^ 1 := by simp
      _ ≤ (d q s) ^ 2 := Nat.pow_le_pow_right hdpos (by omega)
  have hsidepos : 0 < boxSide q s := lt_of_lt_of_le hdpos hdleSide
  have hsidele : boxSide q s ≤ boxVertexCount q s := by
    simp only [boxVertexCount]
    calc
      boxSide q s = (boxSide q s) ^ 1 := by simp
      _ ≤ (boxSide q s) ^ (d q s) :=
        Nat.pow_le_pow_right hsidepos (by omega)
  exact le_trans hs (le_trans hindex (le_trans hdleSide hsidele))

def maxShiftFormula (C q : ℕ) : ℕ :=
  (2 * C - 1) * (10 * C + q)

def periodQ (C q s : ℕ) : ℕ :=
  C * (m q s * (10 * C + q))

def densityCyclesFormula (C q s : ℕ) : ℕ :=
  m q s * maxShiftFormula C q + 1

def admissibleBoxSide (C q s : ℕ) : ℕ :=
  densityCyclesFormula C q s * periodQ C q s

theorem admissibleBoxSide_pos (C q s : ℕ) (hC : 0 < C) (hq : 0 < q) :
    0 < admissibleBoxSide C q s := by
  unfold admissibleBoxSide densityCyclesFormula periodQ m
  apply Nat.mul_pos
  · exact Nat.succ_pos _
  · exact Nat.mul_pos hC (Nat.mul_pos (pow_pos hq _) (by omega))

def admissibleVertexCount (C q s : ℕ) : ℕ :=
  admissibleBoxSide C q s ^ d q s

def admissibleAugmentedSize (C q s P : ℕ) : ℕ :=
  2 * admissibleVertexCount C q s ^ P

noncomputable def admissibleArithmeticData (C q s : ℕ)
    [Fact (Nat.Prime q)] (hC : 0 < C) (hsmall : 40 * C < q) :
    AppendixBColor.ArithmeticBoxData C :=
  toArithmeticBoxData C q s (admissibleBoxSide C q s) hC (by
    exact admissibleBoxSide_pos C q s hC (Fact.out : Nat.Prime q).pos) hsmall

@[simp]
theorem admissibleArithmeticData_Q (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    (admissibleArithmeticData C q s hC hsmall).Q = periodQ C q s := by
  change C * (m q s * q + 10 * C * m q s) =
    C * (m q s * (10 * C + q))
  ring

@[simp]
theorem admissibleArithmeticData_densityCycles (C q s : ℕ)
    [Fact (Nat.Prime q)] (hC : 0 < C) (hsmall : 40 * C < q) :
    (admissibleArithmeticData C q s hC hsmall).densityCycles =
      densityCyclesFormula C q s := by
  simp [admissibleArithmeticData, toArithmeticBoxData, densityCyclesFormula,
    maxShiftFormula, AppendixBColor.ArithmeticBoxData.densityCycles,
    AppendixBColor.ArithmeticBoxData.maxShift,
    AppendixBColor.ArithmeticBoxData.A]

theorem admissibleArithmeticData_p_eq (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    (admissibleArithmeticData C q s hC hsmall).p =
      (admissibleArithmeticData C q s hC hsmall).densityCycles *
        (admissibleArithmeticData C q s hC hsmall).Q := by
  change admissibleBoxSide C q s =
    (admissibleArithmeticData C q s hC hsmall).densityCycles *
      (admissibleArithmeticData C q s hC hsmall).Q
  rw [admissibleArithmeticData_densityCycles, admissibleArithmeticData_Q]
  rfl

noncomputable def finiteData (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) : AppendixBFiniteData C :=
  let D := admissibleArithmeticData C q s hC hsmall
  D.toAppendixBFiniteData D.densityCycles
    (admissibleArithmeticData_p_eq C q s hC hsmall) D.densityCycles_dense

@[simp]
theorem finiteData_n (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    (finiteData C q s hC hsmall).n = admissibleVertexCount C q s := by
  simp [finiteData, admissibleVertexCount, admissibleArithmeticData,
    toArithmeticBoxData, admissibleBoxSide, d,
    AppendixBColor.ArithmeticBoxData.toAppendixBFiniteData,
    AppendixBColor.ArithmeticBoxData.toBoxConstructionData,
    AppendixBConstruction.BoxConstructionData.toAppendixBFiniteData,
    AppendixBConstruction.BoxConstructionData.n]

@[simp]
theorem finiteData_t (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    (finiteData C q s hC hsmall).t = t q s := rfl

theorem log_augmented_of_bounds
    {p d Lp Ld P : ℕ} (hp : 0 < p)
    (hpBound : p ≤ 2 ^ Lp) (hdBound : d ≤ 2 ^ Ld) :
    Nat.log 2 (2 * (p ^ d) ^ P) + 1 ≤ 2 ^ (P + Lp + Ld + 2) := by
  let E := 1 + p * d * P
  have hbase : p ≤ 2 ^ p := nat_le_two_pow p
  have haug_le : 2 * (p ^ d) ^ P ≤ 2 ^ E := by
    calc
      2 * (p ^ d) ^ P = 2 * p ^ (d * P) := by rw [pow_mul]
      _ ≤ 2 * (2 ^ p) ^ (d * P) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase _)
      _ = 2 ^ E := by
        simp only [E]
        rw [← pow_mul, show 1 + p * d * P = 1 + p * (d * P) by ring, pow_add]
        norm_num
  have haug_pos : 0 < 2 * (p ^ d) ^ P := by positivity
  have hlog : Nat.log 2 (2 * (p ^ d) ^ P) + 1 ≤ E + 1 := by
    have hstrict : 2 * (p ^ d) ^ P < 2 ^ (E + 1) :=
      lt_of_le_of_lt haug_le (Nat.pow_lt_pow_succ (by omega))
    have := Nat.log_lt_of_lt_pow haug_pos.ne' hstrict
    omega
  have hprod : P * p * d ≤ 2 ^ (P + Lp + Ld) := by
    calc
      P * p * d ≤ 2 ^ P * 2 ^ Lp * 2 ^ Ld :=
        Nat.mul_le_mul (Nat.mul_le_mul (nat_le_two_pow P) hpBound) hdBound
      _ = 2 ^ (P + Lp + Ld) := by rw [← pow_add, ← pow_add]
  have htwo : 2 ≤ 2 ^ (P + Lp + Ld + 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (P + Lp + Ld + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.succ_le_succ (Nat.zero_le _))
  have hprod' : P * p * d ≤ 2 ^ (P + Lp + Ld + 1) :=
    le_trans hprod (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  calc
    Nat.log 2 (2 * (p ^ d) ^ P) + 1 ≤ E + 1 := hlog
    _ = 2 + P * p * d := by simp only [E]; ring
    _ ≤ 2 ^ (P + Lp + Ld + 1) + 2 ^ (P + Lp + Ld + 1) :=
      Nat.add_le_add htwo hprod'
    _ = 2 ^ (P + Lp + Ld + 2) := by
      rw [show P + Lp + Ld + 2 = (P + Lp + Ld + 1) + 1 by omega, pow_succ]
      ring

def sideGrowthConstant (C q : ℕ) : ℕ :=
  (maxShiftFormula C q + 1) * C * (10 * C + q)

theorem admissibleBoxSide_le_mul_sq (C q s : ℕ)
    (hq : 0 < q) (hC : 0 < C) :
    admissibleBoxSide C q s ≤ sideGrowthConstant C q * (m q s) ^ 2 := by
  have hm : 0 < m q s := pow_pos hq _
  have hcycles : densityCyclesFormula C q s ≤
      m q s * (maxShiftFormula C q + 1) := by
    simp only [densityCyclesFormula]
    calc
      m q s * maxShiftFormula C q + 1 ≤
          m q s * maxShiftFormula C q + m q s := Nat.add_le_add_left hm _
      _ = m q s * (maxShiftFormula C q + 1) := by ring
  unfold admissibleBoxSide periodQ sideGrowthConstant
  calc
    densityCyclesFormula C q s * (C * (m q s * (10 * C + q))) ≤
        (m q s * (maxShiftFormula C q + 1)) *
          (C * (m q s * (10 * C + q))) :=
      Nat.mul_le_mul_right _ hcycles
    _ = (maxShiftFormula C q + 1) * C * (10 * C + q) * (m q s) ^ 2 := by ring

theorem m_le_two_pow (hq : 2 ≤ q) :
    m q s ≤ 2 ^ (q * (2 * s + 2)) := by
  simp only [m]
  calc
    q ^ (2 * (s + 1)) ≤ (2 ^ q) ^ (2 * (s + 1)) :=
      Nat.pow_le_pow_left (nat_le_two_pow q) _
    _ = 2 ^ (q * (2 * (s + 1))) := (pow_mul 2 q (2 * (s + 1))).symm
    _ = 2 ^ (q * (2 * s + 2)) := by congr 1 <;> ring

theorem admissibleBoxSide_le_two_pow (C q s : ℕ)
    (hC : 0 < C) (hq : 2 ≤ q) :
    admissibleBoxSide C q s ≤
      2 ^ (sideGrowthConstant C q + 2 * (q * (2 * s + 2))) := by
  have hmul := admissibleBoxSide_le_mul_sq C q s (by omega) hC
  have hm := m_le_two_pow q s hq
  calc
    admissibleBoxSide C q s ≤ sideGrowthConstant C q * (m q s) ^ 2 := hmul
    _ ≤ 2 ^ (sideGrowthConstant C q) * (2 ^ (q * (2 * s + 2))) ^ 2 :=
      Nat.mul_le_mul (nat_le_two_pow (sideGrowthConstant C q))
        (Nat.pow_le_pow_left hm 2)
    _ = 2 ^ (sideGrowthConstant C q) *
        2 ^ ((q * (2 * s + 2)) * 2) := by
      congr 1
      exact (pow_mul 2 (q * (2 * s + 2)) 2).symm
    _ = 2 ^ (sideGrowthConstant C q + (q * (2 * s + 2)) * 2) :=
      (pow_add 2 (sideGrowthConstant C q) ((q * (2 * s + 2)) * 2)).symm
    _ = 2 ^ (sideGrowthConstant C q + 2 * (q * (2 * s + 2))) := by ring

theorem admissibleMultiplicityGrowth (C q P : ℕ)
    (hC : 0 < C) (hq : 2 ≤ q) :
    DominatesPolylogAlong
      (fun s ↦ admissibleAugmentedSize C q s P)
      (fun s ↦ t q s) := by
  intro c k
  let K := sideGrowthConstant C q
  let A := 6 * q * k
  let B := c + (P + K + 7 * q + 2) * k
  refine ⟨A + B, fun s hs ↦ ?_⟩
  let Lp := K + 2 * (q * (2 * s + 2))
  let Ld := q * (2 * s + 3)
  let L := P + Lp + Ld + 2
  have hp : 0 < admissibleBoxSide C q s := admissibleBoxSide_pos C q s hC (by omega)
  have hlog : Nat.log 2 (admissibleAugmentedSize C q s P) + 1 ≤ 2 ^ L := by
    have := log_augmented_of_bounds hp
      (admissibleBoxSide_le_two_pow C q s hC hq) (d_le_two_pow q s hq) (P := P)
    simpa [admissibleAugmentedSize, admissibleVertexCount, L, Lp, Ld] using this
  have hA : A ≤ s := le_trans (Nat.le_add_right A B) hs
  have hB : B ≤ s := le_trans (Nat.le_add_left B A) hs
  have hlinear : 6 * q * k * s ≤ s * s := Nat.mul_le_mul_right s hA
  have hexp : c + L * k ≤ (s + 1) * (s + 1) := by
    calc
      c + L * k = 6 * q * k * s + B := by
        simp only [L, Lp, Ld, K, B]
        ring
      _ ≤ s * s + s := Nat.add_le_add hlinear hB
      _ ≤ (s + 1) * (s + 1) := by nlinarith
  calc
    c * (Nat.log 2 (admissibleAugmentedSize C q s P) + 1) ^ k ≤
        2 ^ c * (2 ^ L) ^ k :=
      Nat.mul_le_mul (nat_le_two_pow c) (Nat.pow_le_pow_left hlog k)
    _ = 2 ^ (c + L * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((s + 1) * (s + 1)) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ q ^ ((s + 1) * (s + 1)) := Nat.pow_le_pow_left hq _
    _ = t q s := rfl

theorem admissibleVertexCountSizesGrow (C q : ℕ)
    (hC : 0 < C) (hq : 2 ≤ q) :
    SizesTendToInfinity (fun s ↦ admissibleVertexCount C q s) := by
  intro N
  refine ⟨N, fun s hs ↦ ?_⟩
  have hdpos : 0 < d q s := by rw [d_eq_pow]; positivity
  have hp : 0 < admissibleBoxSide C q s := admissibleBoxSide_pos C q s hC (by omega)
  have hdleQ : d q s ≤ periodQ C q s := by
    unfold d periodQ
    have hA : q ≤ 10 * C + q := Nat.le_add_left _ _
    calc
      m q s * q ≤ m q s * (10 * C + q) := Nat.mul_le_mul_left _ hA
      _ ≤ C * (m q s * (10 * C + q)) := by
        have hCone : 1 ≤ C := hC
        calc
          m q s * (10 * C + q) = 1 * (m q s * (10 * C + q)) := by simp
          _ ≤ C * (m q s * (10 * C + q)) :=
            Nat.mul_le_mul_right _ hCone
  have hcycleOne : 1 ≤ densityCyclesFormula C q s := by
    unfold densityCyclesFormula
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hdleSide : d q s ≤ admissibleBoxSide C q s := by
    unfold admissibleBoxSide
    calc
      d q s ≤ periodQ C q s := hdleQ
      _ = 1 * periodQ C q s := by simp
      _ ≤ densityCyclesFormula C q s * periodQ C q s :=
        Nat.mul_le_mul_right _ hcycleOne
  have hsidele : admissibleBoxSide C q s ≤ admissibleVertexCount C q s := by
    unfold admissibleVertexCount
    calc
      admissibleBoxSide C q s = admissibleBoxSide C q s ^ 1 := by simp
      _ ≤ admissibleBoxSide C q s ^ d q s :=
        Nat.pow_le_pow_right hp (by omega)
  exact le_trans hs (le_trans (index_le_d q s hq) (le_trans hdleSide hsidele))

noncomputable def finiteSequence (C q : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) : ℕ → AppendixBFiniteData C :=
  fun s ↦ finiteData C q s hC hsmall

@[simp]
theorem finiteSequence_n (C q : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) (s : ℕ) :
    (finiteSequence C q hC hsmall s).n = admissibleVertexCount C q s :=
  finiteData_n C q s hC hsmall

@[simp]
theorem finiteSequence_t (C q : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) (s : ℕ) :
    (finiteSequence C q hC hsmall s).t = t q s :=
  finiteData_t C q s hC hsmall

theorem finiteSequence_baseSizesGrow (C q : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    SizesTendToInfinity fun s ↦ (finiteSequence C q hC hsmall s).n := by
  simpa using admissibleVertexCountSizesGrow C q hC (by omega)

theorem finiteSequence_multiplicityGrowth (C q : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    ∀ P, 0 < P →
      DominatesPolylogAlong
        (fun s ↦ 2 * ((finiteSequence C q hC hsmall s).n) ^ P)
        (fun s ↦ (finiteSequence C q hC hsmall s).t) := by
  intro P _hP
  simpa [admissibleAugmentedSize] using
    admissibleMultiplicityGrowth C q P hC (by omega)

theorem matching_dense_of_loss {C : ℕ}
    (D : AppendixBColor.ArithmeticBoxData C) (lossNum lossDen : ℕ)
    (hlt : lossNum < lossDen)
    (hloss : lossDen * (10 * C + 1) ≤ lossNum * D.q)
    (hp : D.p = D.densityCycles * D.Q) :
    (lossDen - lossNum) * D.p ^ (D.m * D.q) ≤
      lossDen * (C * D.commonMatchingSize D.densityCycles) := by
  let cycles := D.densityCycles
  let pow := D.p ^ (D.m * D.q - 1)
  have hmOne : 1 ≤ D.m := D.m_pos
  have hqOne : 1 ≤ D.q := D.q_pos
  have hqEq : D.q - 1 + 1 = D.q := Nat.sub_add_cancel hqOne
  have hcycles : D.m * D.maxShift < cycles := by
    simp only [cycles, AppendixBColor.ArithmeticBoxData.densityCycles]
    omega
  have hboundaryLe : D.m * D.maxShift ≤ cycles * D.m := by
    calc
      D.m * D.maxShift ≤ cycles := Nat.le_of_lt hcycles
      _ = cycles * 1 := by simp
      _ ≤ cycles * D.m := Nat.mul_le_mul_left cycles hmOne
  have hcoeffLower :
      cycles * D.m * (D.q - 1) ≤
        cycles * D.B - D.m * D.maxShift := by
    apply Nat.le_sub_of_add_le
    calc
      cycles * D.m * (D.q - 1) + D.m * D.maxShift ≤
          cycles * D.m * (D.q - 1) + cycles * D.m :=
        Nat.add_le_add_left hboundaryLe _
      _ = cycles * D.B := by
        simp only [AppendixBColor.ArithmeticBoxData.B]
        conv_rhs => rw [← hqEq]
        ring
  have hbase :
      (lossDen - lossNum) * D.A ≤ lossDen * (D.q - 1) := by
    change (lossDen - lossNum) * (10 * C + D.q) ≤
      lossDen * (D.q - 1)
    have hdenEq : lossDen - lossNum + lossNum = lossDen :=
      Nat.sub_add_cancel (Nat.le_of_lt hlt)
    nlinarith
  have hcoeff :
      (lossDen - lossNum) * D.p ≤
        lossDen * C * (cycles * D.B - D.m * D.maxShift) := by
    calc
      (lossDen - lossNum) * D.p =
          (cycles * C * D.m) * ((lossDen - lossNum) * D.A) := by
        rw [hp]
        simp only [cycles, AppendixBColor.ArithmeticBoxData.Q]
        rw [D.P_eq_mul_A]
        ring
      _ ≤ (cycles * C * D.m) * (lossDen * (D.q - 1)) :=
        Nat.mul_le_mul_left _ hbase
      _ = lossDen * C * (cycles * D.m * (D.q - 1)) := by ring
      _ ≤ lossDen * C *
          (cycles * D.B - D.m * D.maxShift) :=
        Nat.mul_le_mul_left _ hcoeffLower
  have hdOne : 1 ≤ D.m * D.q := Nat.mul_pos D.m_pos D.q_pos
  have hdEq : D.m * D.q = (D.m * D.q - 1) + 1 :=
    (Nat.sub_add_cancel hdOne).symm
  have hpower : D.p ^ (D.m * D.q) = D.p * pow := by
    rw [hdEq, pow_succ]
    simp only [pow]
    ring
  have hmatching : D.commonMatchingSize cycles =
      (cycles * D.B - D.m * D.maxShift) * pow := by
    unfold AppendixBColor.ArithmeticBoxData.commonMatchingSize
      AppendixBColor.ArithmeticBoxData.totalColorCount
      AppendixBColor.ArithmeticBoxData.maxBoundaryLoss
    rw [Nat.mul_sub_right_distrib]
    simp only [pow]
    ring
  calc
    (lossDen - lossNum) * D.p ^ (D.m * D.q) =
        ((lossDen - lossNum) * D.p) * pow := by rw [hpower]; ring
    _ ≤ (lossDen * C *
        (cycles * D.B - D.m * D.maxShift)) * pow :=
      Nat.mul_le_mul_right pow hcoeff
    _ = lossDen * (C * D.commonMatchingSize D.densityCycles) := by
      change _ = lossDen * (C * D.commonMatchingSize cycles)
      rw [hmatching]
      ring

@[simp]
theorem finiteData_r (C q s : ℕ) [Fact (Nat.Prime q)]
    (hC : 0 < C) (hsmall : 40 * C < q) :
    (finiteData C q s hC hsmall).r =
      (admissibleArithmeticData C q s hC hsmall).commonMatchingSize
        (admissibleArithmeticData C q s hC hsmall).densityCycles := by
  rfl

theorem finiteData_matching_dense (C q lossNum lossDen s : ℕ)
    [Fact (Nat.Prime q)] (hC : 0 < C) (hsmall : 40 * C < q)
    (hlt : lossNum < lossDen)
    (hloss : lossDen * (10 * C + 1) ≤ lossNum * q) :
    (lossDen - lossNum) * (finiteData C q s hC hsmall).n ≤
      lossDen * (C * (finiteData C q s hC hsmall).r) := by
  let D := admissibleArithmeticData C q s hC hsmall
  have hdense := matching_dense_of_loss D lossNum lossDen hlt (by
    simpa [D, admissibleArithmeticData, toArithmeticBoxData] using hloss)
    (admissibleArithmeticData_p_eq C q s hC hsmall)
  simpa [finiteData_n, finiteData_r, admissibleVertexCount, D,
    admissibleArithmeticData, toArithmeticBoxData, d] using hdense

theorem finiteSequence_matching_dense (C q lossNum lossDen : ℕ)
    [Fact (Nat.Prime q)] (hC : 0 < C) (hsmall : 40 * C < q)
    (hlt : lossNum < lossDen)
    (hloss : lossDen * (10 * C + 1) ≤ lossNum * q) :
    ∀ s,
      (lossDen - lossNum) * (finiteSequence C q hC hsmall s).n ≤
        lossDen * (C * (finiteSequence C q hC hsmall s).r) := by
  intro s
  exact finiteData_matching_dense C q lossNum lossDen s hC hsmall hlt hloss

theorem exists_prime_alphabet_for_loss (C lossDen : ℕ) :
    ∃ q, 40 * C < q ∧ lossDen * (10 * C + 1) < q ∧ Nat.Prime q := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes
    (max (40 * C + 1) (lossDen * (10 * C + 1) + 1))
  refine ⟨q, ?_, ?_, hprime⟩
  · have := le_trans (le_max_left (40 * C + 1) _) hq
    omega
  · have := le_trans (le_max_right (40 * C + 1) _) hq
    omega

theorem exists_appendixBSequenceData
    (C lossNum lossDen : ℕ) (hC : 0 < C)
    (hnum : 0 < lossNum) (hlt : lossNum < lossDen) :
    ∃ D : AppendixBSequenceData C,
      D.relativeLossNumerator = lossNum ∧
      D.relativeLossDenominator = lossDen := by
  obtain ⟨q, hsmall, hqLoss, hprime⟩ :=
    exists_prime_alphabet_for_loss C lossDen
  letI : Fact (Nat.Prime q) := ⟨hprime⟩
  have hloss : lossDen * (10 * C + 1) ≤ lossNum * q := by
    calc
      lossDen * (10 * C + 1) ≤ q := Nat.le_of_lt hqLoss
      _ = 1 * q := by simp
      _ ≤ lossNum * q := Nat.mul_le_mul_right q hnum
  let D : AppendixBSequenceData C :=
    { finite := finiteSequence C q hC hsmall
      relativeLossNumerator := lossNum
      relativeLossDenominator := lossDen
      relativeLoss_lt := hlt
      matching_dense :=
        finiteSequence_matching_dense C q lossNum lossDen hC hsmall hlt hloss
      baseSizesGrow := finiteSequence_baseSizesGrow C q hC hsmall
      multiplicityGrowth := finiteSequence_multiplicityGrowth C q hC hsmall }
  exact ⟨D, rfl, rfl⟩

theorem exists_denseERSSequence
    (C lossNum lossDen : ℕ) (hC : 0 < C)
    (hnum : 0 < lossNum) (hlt : lossNum < lossDen) :
    ∃ F : DenseERSSequence C,
      F.relativeLossNumerator = lossNum ∧
      F.relativeLossDenominator = lossDen := by
  obtain ⟨D, hnumEq, hdenEq⟩ :=
    exists_appendixBSequenceData C lossNum lossDen hC hnum hlt
  exact ⟨D.toDenseERSSequence, hnumEq, hdenEq⟩

end AppendixBSupports

end ERSFamily

end Formal.Streaming
