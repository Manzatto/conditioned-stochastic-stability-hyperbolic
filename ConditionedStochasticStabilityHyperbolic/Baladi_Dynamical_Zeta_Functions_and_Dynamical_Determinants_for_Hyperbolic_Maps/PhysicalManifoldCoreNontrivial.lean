module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSupportedCore
public import LeanShared.Geometry.SupportedPairingNontrivial

/-! A supported-core packet proves that its analytic space is nontrivial. The smooth integral
identity of the packet is the common distribution pairing on the dense regular core, and a
supported bump at a live point of positive reference measure is a nonzero analytic vector. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
open LeanShared SmoothSupportedManifoldCore

variable {E M Reg : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {V : Set M} {K : Set M} [CompactSpace K] {Tests : Set (K →ᵇ ℝ)} {σ : Measure K}
  [IsFiniteMeasure σ]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology M] [T2Space M]
  [CompleteSpace Reg] in
/-- The analytic space of a supported-core packet is nontrivial. -/
theorem CoreData.nontrivial {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {q : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] Reg}
    {qa : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] H}
    (p : CoreData (K := K) (Tests := Tests) (σ := σ) q qa)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ)) (hphysical : ∀ c, physical (q c) = physicalCore V K c)
    (dense : DenseRange q) (hK : IsClosed K) (hV : IsOpen V) (x : K) (hx : x.val ∈ V)
    (hpositive : {y : K | y.val ∈ V} ⊆ σ.support) : Nontrivial H :=
  nontrivial_of_common_distribution_pairing hK hV x hx σ q physical hphysical hpositive qa
    p.embedding (fun c => by
      apply DFunLike.coe_injective
      refine dense.equalizer (p.embedding (qa c)).continuous
        (SupportedRegularPairing.embedding σ physical (physicalCore V K c)).continuous
        (funext fun d => ?_)
      simp only [Function.comp_apply, SupportedRegularPairing.embedding_apply, hphysical]
      rw [p.smoothPairing]
      rfl)

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCore
