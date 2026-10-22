module

public import LeanShared.Dynamics.OneSidedGraphPaths
public import LeanShared.Dynamics.SymbolicFuturePotentialVariation

/-! The explicit regular future cohomology potential descends to the
actual one-sided graph system, with exact values, continuity, and
exponential prefix variation.  This is the potential to which the
one-sided weighted transfer operator can be applied.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {R : A → A → Prop}

@[expose] def HasExponentialPrefixVariations (ψ : FuturePath R → ℝ) : Prop :=
  ∃ rate > 0, rate < 1 ∧ ∃ C ≥ 0,
    ∀ radius : ℕ, ∀ a b : FuturePath R, PrefixAgreement a b radius → |ψ b - ψ a| ≤ C * rate ^ radius

@[expose] def oneSidedPotential (φ : Path R → ℝ) (a : FuturePath R) : ℝ :=
  futurePotential φ (futureExtension a)

omit [DiscreteTopology A] in
theorem oneSidedPotential_restriction (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (a : Path R) : oneSidedPotential φ (futureRestriction a) = futurePotential φ a := by
  apply futurePotential_depends_on_future φ variation
  intro n nonnegative
  rw [futureExtension_restriction, pastReset_future a n nonnegative]

theorem oneSidedPotential_continuous (φ : Path R → ℝ) (continuous : Continuous φ)
    (variation : HasExponentialVariations φ) : Continuous (oneSidedPotential φ) :=
  (futurePotential_continuous φ continuous variation).comp futureExtension_continuous

theorem oneSidedPotential_exponential [CompactSpace A] (φ : Path R → ℝ)
    (continuous : Continuous φ) (variation : HasExponentialVariations φ) :
    HasExponentialPrefixVariations (oneSidedPotential φ) := by
  obtain ⟨rate, positive, small, C, nonnegative, bound⟩ :=
    futurePotential_hasExponentialVariations φ continuous variation
  refine ⟨rate, positive, small, C, nonnegative, fun radius a b same => ?_⟩
  exact bound radius (futureExtension a) (futureExtension b) (futureExtension_window a b radius same)

omit [DiscreteTopology A] in
theorem oneSidedPotential_cohomology (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (a : Path R) : φ a = oneSidedPotential φ (futureRestriction a) +
      resetTransfer φ a - resetTransfer φ (shift R a) := by
  rw [oneSidedPotential_restriction φ variation]
  exact futurePotential_cohomology φ a

end LeanShared.BilateralShadowingCoding
