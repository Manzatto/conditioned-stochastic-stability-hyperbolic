module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedNormalizedGap

/-! Equality of actual represented kernels and prefix sets transports the
produced datum and its ambient product together. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixDataTransport
open ComplexStrongFeller LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

 theorem transport {C D : AbsorbingMarkovChains.CanonicalChain X}
    (sfC : HasStrongFellerKernel C) (sfD : HasStrongFellerKernel D) (eqC : C = D)
    {P Q : Set X} [CompactSpace P] [CompactSpace Q]
    (hP : MeasurableSet P) (hQ : MeasurableSet Q) (eqP : P = Q)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain C P hP) (RestrictedLayerChain.strongFeller C sfC P hP))
      (1 : P →ᵇ ℝ)) (Λ : Set X)
    (positive : ∀ x : P, x.val ∈ Λ → 0 < d.eigenvector x) :
    ∃ e : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain D Q hQ) (RestrictedLayerChain.strongFeller D sfD Q hQ))
      (1 : Q →ᵇ ℝ),
      (∀ x : Q, x.val ∈ Λ → 0 < e.eigenvector x) ∧
      (productMeasure (RestrictedLayerChain.chain D Q hQ)
        (RestrictedLayerChain.strongFeller D sfD Q hQ) e).map Subtype.val =
      (productMeasure (RestrictedLayerChain.chain C P hP)
        (RestrictedLayerChain.strongFeller C sfC P hP) d).map Subtype.val := by
  subst D
  subst Q
  exact ⟨d, positive, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Global.PrefixDataTransport
