module

public import LeanShared.Dynamics.BasicHyperbolicUniqueGibbsMeasure
public import LeanShared.Dynamics.EquilibriumCoboundary
public import LeanShared.Dynamics.HyperbolicThermodynamics

/-! Actual construction of the thermodynamic package. A fractional reference potential and a
continuous volume-change coboundary suffice; the actual Riemannian potential is never required
to be Hölder for a merely continuous metric. Pressure, equilibrium and uniqueness are proved. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle NNReal BoundedContinuousFunction
open ThermodynamicDefinitions

set_option maxHeartbeats 1600000 in
theorem BasicData.exists_equilibriumPackage_of_coboundary
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ) (g ψ : M → ℝ)
    (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    (u : M → ℝ) (continuousU : Continuous u)
    (same : ∀ x ∈ Λ, b.hyperbolic.potential g x = ψ x + u x - u (T x)) :
    Nonempty (EquilibriumPackage b.hyperbolic g) := by
  obtain ⟨_, _, P, pressureP, _, _, _, _, ν, state, _, unique, _⟩ :=
    b.exists_unique_gibbs_equilibrium forward inverse mixing ψ α positiveα smallα regular
  let v : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨u, continuousU⟩
  have bounded (x : M) (_hx : x ∈ Λ) : |u x| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    change ‖v x‖ ≤ ‖v‖
    exact v.norm_coe_le_norm x
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  have pressureSame := pressure_coboundary invariant
    ‖v‖ bounded same
  have transfer (η : ProbabilityMeasure M) :
      IsEquilibriumState T (b.hyperbolic.potential g) Λ η ↔ IsEquilibriumState T ψ Λ η :=
    isEquilibriumState_iff_coboundary T Λ invariant
      (b.hyperbolic.potential g) ψ u ‖v‖ bounded same η (v.integrable (η : Measure M))
  refine ⟨⟨P, pressureSame.trans pressureP, ν.map Subtype.val,
    (transfer _).mpr state, ?_⟩⟩
  intro η equilibrium
  exact unique η ((transfer η).mp equilibrium)

end LeanShared.HyperbolicBasicSet
