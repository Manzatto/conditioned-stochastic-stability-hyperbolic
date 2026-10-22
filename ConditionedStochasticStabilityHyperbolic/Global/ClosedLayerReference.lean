module

public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Actual closed-layer densities and reference-null stratum complements

The full weighted noisy kernel's actual density pulls back to every closed
layer with its natural reference measure. The proved ambient null closure
addition then becomes exactly the relative-null premise used by the
closed-layer spectral-growth to actual-stratum bridge.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionedStochasticStabilityHyperbolic.Global.ClosedLayerReference
open RestrictedLayerChain
variable {X : Type*} [MeasurableSpace X]

/-- Actual density laws restrict to the exact closed-layer chain; the
reference measure is ambient volume pulled back under state inclusion. -/
theorem restricted_density_law
    (C : AbsorbingMarkovChains.CanonicalChain X) (K : Set X) (hK : MeasurableSet K)
    (σ : Measure X) (q : X × X → ENNReal)
    (htransition : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y))) :
    ∀ x : K, (chain C K hK).killedTransition x =
      (σ.comap (Subtype.val : K → X)).withDensity (fun y : K => q (x.val, y.val)) := by
  intro x
  rw [killedTransition, LeanShared.SubtypeKernel.restrict_apply, htransition x.val]
  ext S hS
  rw [(MeasurableEmbedding.subtype_coe hK).comap_apply,
    withDensity_apply _ ((MeasurableEmbedding.subtype_coe hK).measurableSet_image' hS),
    withDensity_apply _ hS]
  exact (setLIntegral_subtype hK S (fun y => q (x.val, y))).symm

/-- Ambient closure discrepancy nullity is exactly relative stratum
complement nullity in the closed-layer reference measure. -/
theorem relative_stratum_complement_zero
    (σ : Measure X) (S K : Set X) (hK : MeasurableSet K)
    (hnull : σ (K \ S) = 0) :
    (σ.comap (Subtype.val : K → X)) (Subtype.val ⁻¹' S)ᶜ = 0 := by
  rw [(MeasurableEmbedding.subtype_coe hK).comap_apply]
  have he : (Subtype.val : K → X) '' (Subtype.val ⁻¹' S)ᶜ = K \ S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [he]
  exact hnull

end ConditionedStochasticStabilityHyperbolic.Global.ClosedLayerReference
