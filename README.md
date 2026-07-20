# Semi-Streaming Matching in a Single Pass: Greedy is Optimal

A Lean 4 formalization of

- *Semi-Streaming Matching in a Single Pass I: A New Framework for Lower Bounds via
  Blueprints* ([arXiv:2607.14644](https://arxiv.org/abs/2607.14644))
- *Semi-Streaming Matching in a Single Pass II: Greedy is Optimal*
  ([arXiv:2607.14656](https://arxiv.org/abs/2607.14656))

by Sepehr Assadi, Max Jiang, and Mars Xiang. This is an independent formalization
effort, separate from the papers, created by Max Jiang and Mars Xiang.

## Statement

The main theorem is `greedy_is_optimal`, in
[`SemiStreamingMatching.lean`](SemiStreamingMatching.lean):

```lean
theorem greedy_is_optimal {δ : ℚ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ (ε : ℚ) (size : ℕ → ℕ), 0 < ε ∧ SizesTendToInfinity size ∧
      ∀ A : SemiStreamingAlgorithm, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ (G : BipartiteGraph (Fin (size n)) (Fin (size n))) (σ : G.EdgeStream),
          A.successProbability (1 / 2 + δ) G σ ≤ 1 - ε
```

For any $0 < \delta \le 1/2$, there exists $\varepsilon > 0$ and a family of input
graphs whose sizes tend to infinity such that for every (possibly randomized)
one-pass semi-streaming algorithm $A$, there is a size $n_0$ where for every input
graph in the family with size at least $n_0$, algorithm $A$ returns a
$\ge 1/2 + \delta$ approximation with probability at most $1 - \varepsilon$.

## Building

```sh
lake exe cache get
lake build
```
