module
public import LeanShared.Dynamics.BasicHyperbolicPartitionExponentialUpper
public import LeanShared.Dynamics.PressureRestriction
public import Mathlib.Topology.TietzeExtension

/-! The actual partition upper bound needs continuity only on the core. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BoundedContinuousFunction
open ThermodynamicDefinitions

theorem BasicData.eventual_core_partition_exponential_upper
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (continuous : ContinuousOn ψ Λ) :
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∀ ε > 0, ∀ η > 0,
      ∀ᶠ n : ℕ in Filter.atTop, separatedPartitionSum T ψ Λ (n + 1) ε ≤
        ENNReal.ofReal (Real.exp (((n + 1 : ℕ) : ℝ) * (P + η))) := by
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let f : Λ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨(fun x => ψ x.val), continuous.domRestrict⟩
  obtain ⟨g, _, extension⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding
    b.hyperbolic.compact.isClosed.isClosedEmbedding_subtypeVal
  have agreement : EqOn ψ g Λ := by
    intro x hx
    exact (congrFun extension ⟨x,hx⟩).symm
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  obtain ⟨P, pressureP, upper⟩ := b.eventual_partition_exponential_upper forward inverse g g.continuous
  refine ⟨P, (pressure_eq_of_eqOn invariant agreement).trans pressureP, fun ε hε η hη => ?_⟩
  simpa only [separatedPartitionSum_eq_of_eqOn invariant agreement] using upper ε hε η hη

end LeanShared.HyperbolicBasicSet
