module
public import LeanShared.Analysis.BTLinkedDyadicWeights
public import Mathlib.Tactic.Linarith

/-! Scalar choice of the ordinary order `b₀` and inverse-test order `a` compatible with all three
tower stages and the order-`b₀` physical tests. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.NativeSourceOrders

/-- A single ordinary exponent supports all three tower stages and leaves
room for the higher inverse-test interpolation order. -/
theorem choose_orders
    (t s δ α q r : ℝ)
    (ht : 0 < t) (hs : s < 0) (hδ : 0 < δ)
    (gap : t - s + (δ + δ) < α)
    (hα1 : α < 1) (hαq : α < q) (hαr : α + 1 < r) :
    ∃ b₀ a : ℝ,
      0 < b₀ ∧ b₀ < 1 ∧ b₀ < q ∧ b₀ < a ∧ a < α ∧
      a < 1 ∧ a < q ∧ a + 1 < r ∧ t < b₀ ∧
      0 < b₀ + s - (δ + δ) := by
  let b₀ : ℝ := (t - s + (δ + δ) + α) / 2
  let a : ℝ := (b₀ + α) / 2
  have lower : t - s + (δ + δ) < b₀ := by
    dsimp [b₀]
    linarith
  have upper : b₀ < α := by
    dsimp [b₀]
    linarith
  have tBelow : t < b₀ := by linarith
  have bPositive : 0 < b₀ := ht.trans tBelow
  have bBelowOne : b₀ < 1 := upper.trans hα1
  have bBelowQ : b₀ < q := upper.trans hαq
  have bBelowA : b₀ < a := by dsimp [a]; linarith
  have aBelowAlpha : a < α := by dsimp [a]; linarith
  have aBelowOne : a < 1 := aBelowAlpha.trans hα1
  have aBelowQ : a < q := aBelowAlpha.trans hαq
  have aBelowR : a + 1 < r := by linarith
  have dual : 0 < b₀ + s - (δ + δ) := by linarith
  exact ⟨b₀, a, bPositive, bBelowOne, bBelowQ, bBelowA, aBelowAlpha,
    aBelowOne, aBelowQ, aBelowR, tBelow, dual⟩

/-- Discharge all finite sign conditions. Use ell = 0, delta, delta+delta for the three stages. -/
theorem stage_conditions
    (t s δ α b₀ ell : ℝ)
    (hs : s < 0) (hδ : 0 < δ) (twoDelta : δ + δ < t)
    (gap : t - s + (δ + δ) < α) (hα1 : α < 1)
    (_hb₀1 : b₀ < 1) (tBelow : t < b₀)
    (dual : 0 < b₀ + s - (δ + δ))
    (ellNonneg : 0 ≤ ell) (ellBound : ell ≤ δ + δ) :
    let e := LeanShared.BTLinkedDyadicWeights.exponent (t - ell) (s - ell)
    (∀ σ, e σ ≤ b₀) ∧
    (∀ σ, 0 < b₀ + e σ) ∧
    (∀ σ τ, e σ - 1 - e τ < 0) ∧
    (∀ σ, -1 - e σ < 0) ∧
    (∀ σ, e σ ≤ 1) ∧
    (∀ σ, 0 < 1 + e σ) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    cases σ <;> simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith
  · intro σ
    cases σ <;> simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith
  · intro σ τ
    cases σ <;> cases τ <;>
      simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith
  · intro σ
    cases σ <;> simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith
  · intro σ
    cases σ <;> simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith
  · intro σ
    cases σ <;> simp only [LeanShared.BTLinkedDyadicWeights.exponent] <;> linarith

end ConditionedStochasticStabilityHyperbolic.NativeSourceOrders
