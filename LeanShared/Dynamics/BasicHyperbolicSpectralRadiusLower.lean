module

public import LeanShared.Dynamics.BasicHyperbolicWeightedIntegralGrowth
public import LeanShared.Analysis.SpectralRadiusFromCoefficients

/-! The proved hyperbolic weighted-integral growth gives the pressure lower
bound for an actual completed transfer operator once its integral matrix
coefficient has been identified. This neither assumes nor proves simplicity,
a leading eigenvector, or an upper spectral-radius bound. -/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal BigOperators
open ThermodynamicDefinitions FractionalManifoldRegularity

theorem BasicData.exp_pressure_le_spectralRadius_from_coefficients
    {E M B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (g : M → ℝ) (weightRegular : Regular (E := E) (F := ℝ) q g)
    (positive : ∀ x ∈ Λ, 0 < g x)
    (P : ℝ) (pressureP : pressure T (b.hyperbolic.potential g) Λ = (P : EReal))
    (operator : B →L[ℂ] B) (pairing : B →L[ℂ] ℂ) (seed : B)
    (coefficient : ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal
        (∏ j ∈ Finset.range (n + 1), g ((T : M → M)^[j] x))
          ∂(referenceMeasure.measure μ)) =
        ENNReal.ofReal ‖pairing ((operator ^ n) seed)‖) :
    ENNReal.ofReal (Real.exp P) ≤ spectralRadius ℂ operator := by
  apply SpectralRadiusFromCoefficients.exp_le_spectralRadius_of_integral_growth
    operator pairing seed P
    (fun n => ∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x))
      ∂(referenceMeasure.measure μ)) coefficient
  intro γ hγ
  obtain ⟨N, positiveN, P', pressureP', lower⟩ :=
    b.exists_weighted_integral_growth regularity weightOrder forwardRegular inverseRegular
      mixing referenceMeasure μ g weightRegular positive γ hγ
  have same : P' = P := EReal.coe_injective (pressureP'.symm.trans pressureP)
  subst P'
  exact ⟨N, positiveN, lower⟩

end LeanShared.HyperbolicBasicSet
