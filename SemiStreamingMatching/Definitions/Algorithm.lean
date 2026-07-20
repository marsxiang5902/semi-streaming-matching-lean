import SemiStreamingMatching.Definitions.Graph
import Mathlib.Data.Rat.Field

namespace Formal.Streaming

variable {L R : Type*}

abbrev BitString (s : ℕ) := Fin (2 ^ s)

structure OnePassAlgorithm (L R : Type*) where
  State : Type
  [stateFintype : Fintype State]
  init : State
  step : State → Edge L R → State
  output : State → Finset (Edge L R)

namespace OnePassAlgorithm

instance (A : OnePassAlgorithm L R) : Fintype A.State := A.stateFintype

def runFrom (A : OnePassAlgorithm L R) (q : A.State)
    (xs : List (Edge L R)) : A.State :=
  xs.foldl A.step q

def run (A : OnePassAlgorithm L R) (xs : List (Edge L R)) : A.State :=
  A.runFrom A.init xs

def result (A : OnePassAlgorithm L R) (xs : List (Edge L R)) :
    Finset (Edge L R) :=
  A.output (A.run xs)

@[simp]
theorem runFrom_nil (A : OnePassAlgorithm L R) (q : A.State) :
    A.runFrom q [] = q :=
  rfl

@[simp]
theorem runFrom_append (A : OnePassAlgorithm L R) (q : A.State)
    (xs ys : List (Edge L R)) :
    A.runFrom q (xs ++ ys) = A.runFrom (A.runFrom q xs) ys := by
  simp [runFrom, List.foldl_append]

theorem run_append (A : OnePassAlgorithm L R)
    (xs ys : List (Edge L R)) :
    A.run (xs ++ ys) = A.runFrom (A.run xs) ys := by
  simp [run, runFrom_append]

def StateEncoding (A : OnePassAlgorithm L R) (s : ℕ) :=
  A.State ↪ BitString s

def UsesBits (A : OnePassAlgorithm L R) (s : ℕ) : Prop :=
  Nonempty (A.StateEncoding s)

theorem UsesBits.stateCard_le {A : OnePassAlgorithm L R} {s : ℕ}
    (h : A.UsesBits s) : Fintype.card A.State ≤ 2 ^ s := by
  obtain ⟨enc⟩ := h
  simpa [StateEncoding, BitString] using Fintype.card_le_of_embedding enc

def MeetsApproximation [Fintype L] [Fintype R]
    (ρ : ℚ) (G : BipartiteGraph L R) (M : Finset (Edge L R)) : Prop :=
  G.IsMatching M ∧
    ρ * (G.matchingNumber : ℚ) ≤ (M.card : ℚ)

def SucceedsOn [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : OnePassAlgorithm L R) (ρ : ℚ) (G : BipartiteGraph L R)
    (σ : G.EdgeStream) : Prop :=
  MeetsApproximation ρ G (A.result σ.order)

def IsApproximation [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : OnePassAlgorithm L R) (ρ : ℚ) : Prop :=
  ∀ (G : BipartiteGraph L R) (σ : G.EdgeStream), A.SucceedsOn ρ G σ

def IsCorrect [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : OnePassAlgorithm L R) : Prop :=
  ∀ (G : BipartiteGraph L R) (σ : G.EdgeStream),
    G.IsMaximumMatching (A.result σ.order)

theorem IsCorrect.isApproximation_one [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {A : OnePassAlgorithm L R} (hA : A.IsCorrect) :
    A.IsApproximation 1 := by
  intro G σ
  refine ⟨(hA G σ).1, ?_⟩
  rw [(hA G σ).2]
  simp [MeetsApproximation]

end OnePassAlgorithm

structure RandomizedOnePassAlgorithm (L R : Type*) where
  State : Type
  [stateFintype : Fintype State]
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedNonempty : Nonempty Seed]
  init : Seed → State
  step : Seed → State → Edge L R → State
  output : Seed → State → Finset (Edge L R)

namespace RandomizedOnePassAlgorithm

instance (A : RandomizedOnePassAlgorithm L R) : Fintype A.State := A.stateFintype
instance (A : RandomizedOnePassAlgorithm L R) : Fintype A.Seed := A.seedFintype
instance (A : RandomizedOnePassAlgorithm L R) : Nonempty A.Seed := A.seedNonempty

def fixSeed (A : RandomizedOnePassAlgorithm L R) (ξ : A.Seed) :
    OnePassAlgorithm L R where
  State := A.State
  stateFintype := A.stateFintype
  init := A.init ξ
  step := A.step ξ
  output := A.output ξ

def UsesBits (A : RandomizedOnePassAlgorithm L R) (s : ℕ) : Prop :=
  Nonempty (A.State ↪ BitString s)

theorem fixSeed_usesBits {A : RandomizedOnePassAlgorithm L R} {s : ℕ}
    (h : A.UsesBits s) (ξ : A.Seed) : (A.fixSeed ξ).UsesBits s :=
  h

noncomputable def successfulSeeds [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) : Finset A.Seed := by
  classical
  exact Finset.univ.filter (fun ξ => (A.fixSeed ξ).SucceedsOn ρ G σ)

noncomputable def successProbability [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) : ℚ :=
  (A.successfulSeeds ρ G σ).card / Fintype.card A.Seed

def IsApproximationWithProbability [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : RandomizedOnePassAlgorithm L R) (ρ p : ℚ) : Prop :=
  ∀ (G : BipartiteGraph L R) (σ : G.EdgeStream),
    p ≤ A.successProbability ρ G σ

theorem successProbability_nonneg [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    0 ≤ A.successProbability ρ G σ := by
  unfold successProbability
  positivity

theorem successProbability_le_one [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (A : RandomizedOnePassAlgorithm L R) (ρ : ℚ)
    (G : BipartiteGraph L R) (σ : G.EdgeStream) :
    A.successProbability ρ G σ ≤ 1 := by
  unfold successProbability
  rw [div_le_one]
  · exact_mod_cast (A.successfulSeeds ρ G σ).card_le_univ
  · exact_mod_cast Fintype.card_pos

end RandomizedOnePassAlgorithm

end Formal.Streaming
