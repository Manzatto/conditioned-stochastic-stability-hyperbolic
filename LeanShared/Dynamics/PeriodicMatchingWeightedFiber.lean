module

public import LeanShared.Dynamics.PeriodicMatchingSignedCoefficient
public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Literal weighted periodic correction over each periodic base point.
The actual correction coding preserves every orbit energy, and the
proved signed coefficient one gives exactly the original exponential
orbit weight.  No zeta or determinant identity is assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization ThermodynamicDefinitions
variable {A X Y : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

omit [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A] in
theorem orbitSum_of_semiconjugacy (f : Y → X) (S : Y → Y) (T : X → X)
    (same : Semiconj f S T) (φ : X → ℝ) (n : ℕ) (y : Y) :
    orbitSum S (φ ∘ f) n y = orbitSum T φ n (f y) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg φ ((same.iterate_right i) y)

theorem periodicMatching_real_signed_coefficient (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    (∑ᶠ a : (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period),
      (-1 : ℝ) ^ a.1 * ((∏ i ∈ Finset.range period, matchingEdgeSign (a.2.val.val.val i)) : ℝ)) = 1 := by
  classical
  let : Finite (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) :=
    periodicMatchingFiberSigma_finite T rectangles code properties x period positive fixed
  let : Fintype (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) := Fintype.ofFinite _
  have rational := periodicMatchingSignedCoefficient_eq_one T rectangles code properties x period positive fixed
  unfold periodicMatchingSignedCoefficient at rational
  rw [finsum_eq_sum_of_fintype] at rational ⊢
  exact_mod_cast rational

@[expose] def periodicMatchingWeightedFiber (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (φ : X → ℝ) (x : X) (period : ℕ) : ℝ :=
  ∑ᶠ a : (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period),
    (-1 : ℝ) ^ a.1 * ((∏ i ∈ Finset.range period, matchingEdgeSign (a.2.val.val.val i)) : ℝ) *
      Real.exp (orbitSum
        (shift (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (a.1 + 1)))
        (φ ∘ matchingCode T rectangles code a.1) period a.2.val.val)

theorem periodicMatchingWeightedFiber_eq (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (φ : X → ℝ)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    periodicMatchingWeightedFiber T rectangles code φ x period = Real.exp (orbitSum T φ period x) := by
  unfold periodicMatchingWeightedFiber
  have energies (a : Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) :
      orbitSum
        (shift (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (a.1 + 1)))
        (φ ∘ matchingCode T rectangles code a.1) period a.2.val.val = orbitSum T φ period x := by
    have identity := orbitSum_of_semiconjugacy (matchingCode T rectangles code a.1)
      (shift (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (a.1 + 1))) T
      (matchingCode_intertwines T rectangles code properties.geometry properties.intertwines a.1) φ period a.2.val.val
    rw [show matchingCode T rectangles code a.1 a.2.val.val = x from a.2.val.property] at identity
    exact identity
  simp_rw [energies]
  rw [← finsum_mul, periodicMatching_real_signed_coefficient T rectangles code properties x period positive fixed, one_mul]

end LeanShared.BilateralShadowingCoding
