module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPrincipalContraction
public import LeanShared.Analysis.IntrinsicPressureCoreComparison

/-! The core term in the BT iterate-pressure formula is the actual HL
unstable-Jacobian potential. The logarithmic comparison follows from the
actual tangent word bounds, not from a supplied pressure contraction. -/
@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

theorem oneStepJacobian_eq (x : M) :
    ((h.differential x).toLinearMap.domRestrict (h.basic.hyperbolic.unstable x)).normDet =
      h.basic.hyperbolic.unstableJacobian x := by
  have hD : (h.differential x).toLinearMap =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap := by
    ext v
    rfl
  rw [hD]
  symm
  exact LinearMap.normDet_codRestrict _

theorem log_principal_density_le (envelope : M → ℝ)
    (positive : ∀ x ∈ Λ, 0 < envelope x)
    (dimension : ∀ x ∈ Λ, 0 < Module.finrank ℝ (h.basic.hyperbolic.unstable x))
    (N : ℕ) (t s C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (bound : ∀ x ∈ Λ, max
      (IntrinsicPrincipalDensity.stableFactor (fun _ : Unit => (T : M → M))
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) (List.replicate N ()) x
        (h.basic.hyperbolic.stable (IntrinsicPrincipalDensity.orbit
          (fun _ : Unit => (T : M → M)) (List.replicate N ()) x)) ^ t)
      (IntrinsicPrincipalDensity.inverseFactor (fun _ : Unit => (T : M → M))
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) (List.replicate N ()) x
        (h.basic.hyperbolic.unstable x) ^ (-s)) ≤ C * γ ^ N) :
    ∀ x ∈ Λ,
      Real.log (IntrinsicPrincipalDensity.density (fun _ : Unit => (T : M → M))
        (fun y => TangentSpace (𝓘(ℝ, E)) y) (fun _ => h.differential) envelope
        h.basic.hyperbolic.stable h.basic.hyperbolic.unstable N t s ((fun _ => ()), x)) ≤
      ThermodynamicDefinitions.orbitSum T (h.basic.hyperbolic.potential envelope) N x +
        (Real.log C + (N : ℝ) * Real.log γ) := by
  intro x hx
  have hK : ∀ _ : Unit, MapsTo T Λ Λ := fun _ _ hy =>
    h.basic.hyperbolic.invariant ▸ Set.mem_image_of_mem T hy
  have hinv : ∀ (_ : Unit) y, y ∈ Λ → (h.basic.hyperbolic.unstable y).map
      (h.differential y).toLinearMap = h.basic.hyperbolic.unstable (T y) := by
    intro _ y hy
    have hD : (h.differential y).toLinearMap =
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T y).toLinearMap := by ext v; rfl
    rw [hD]
    exact h.basic.hyperbolic.unstable_invariant y hy
  have hψ : (fun y => Real.log (envelope y) -
      Real.log (((h.differential y).toLinearMap.domRestrict (h.basic.hyperbolic.unstable y)).normDet)) =
      h.basic.hyperbolic.potential envelope := by
    funext y
    rw [h.oneStepJacobian_eq y]
    rfl
  simpa only [hψ] using IntrinsicPrincipalDensity.log_density_le_orbitSum
    (fun _ : Unit => (T : M → M)) (fun y => TangentSpace (𝓘(ℝ, E)) y)
    (fun _ => h.differential) envelope Λ () hK positive h.basic.hyperbolic.stable
    h.basic.hyperbolic.unstable hinv dimension N t s C γ hC hγ x hx (bound x hx)

end ConditionedStochasticStabilityHyperbolic.Paper.HL
