module
public import LeanShared.Analysis.ActualWordWeightProduct
public import LeanShared.Analysis.FiniteJetWords
public import LeanShared.Analysis.ActualWordMicrolocalBound

/-! The same literal finite noisy word appears in three encodings: a prefix
orbit indexed by the controls, a prefix orbit indexed by positions, and a
composition of a sequence of maps extended past the horizon. They agree at
every time up to the horizon, and the accumulated weight is the same finite
product. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared CylinderPrincipalCoefficient

variable {G X : Type*}

theorem prefixOrbit_reindex (F : G → X → X) {N : ℕ} (word : Fin N → G) (k : ℕ) (x : X) :
    prefixOrbit F word k x = prefixOrbit (fun j : Fin N => F (word j)) (fun j => j) k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < N
    · simp only [prefixOrbit, dite_eq_left hk, ih]
    · simp only [prefixOrbit, dite_eq_right hk, ih]

theorem prefixOrbit_eq_jetWord (F : G → X → X) {N : ℕ} (word : Fin N → G) (extension : ℕ → G)
    (agree : ∀ n (h : n < N), extension n = word ⟨n, h⟩) :
    ∀ k ≤ N, ∀ x, prefixOrbit F word k x = FiniteJetComposition.word (fun n => F (extension n)) k x := by
  intro k
  induction k with
  | zero => intro _ x; rfl
  | succ k ih =>
    intro hk x
    have lt : k < N := Nat.lt_of_succ_le hk
    simp only [prefixOrbit, dite_eq_left lt, FiniteJetComposition.word, Function.comp_apply,
      ih (Nat.le_of_lt lt) x, agree k lt]

theorem weight_ofFn_eq_range (F : G → X → X) (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x : X) :
    ActualFiniteRegularWord.weight F g (List.ofFn word) x =
      ((∏ k ∈ Finset.range N, g (prefixOrbit F word k x) : ℝ) : ℂ) := by
  rw [← ActualWordMicrolocalBound.realWeight_cast,
    ActualWordWeightProduct.realWeight_ofFn_eq_product,
    Fin.prod_univ_eq_prod_range (fun k => g (prefixOrbit F word k x))]

theorem realWeight_ofFn_eq_range (F : G → X → X) (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x : X) :
    ActualWordMicrolocalBound.realWeight F g (List.ofFn word) x =
      ∏ k ∈ Finset.range N, g (prefixOrbit F word k x) := by
  rw [ActualWordWeightProduct.realWeight_ofFn_eq_product,
    Fin.prod_univ_eq_prod_range (fun k => g (prefixOrbit F word k x))]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
