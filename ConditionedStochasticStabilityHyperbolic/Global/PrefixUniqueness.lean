module

public import ConditionedStochasticStabilityHyperbolic.Global.AmbientPrefixEigenfunction
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixQuasiErgodic

/-!
# Qualified full-process uniqueness of a selected prefix product

The original process may have several QEMs. A candidate whose support meets
an interior positive point of the selected prefix equals that prefix product.
No leading spectral gap for the entire ambient process is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixUniqueness
open AbsorbingMarkovChains ComplexStrongFeller RestrictedLayerChain
open LayerQuasiErgodic AmbientPrefixEigenfunction PrefixCorrespondence PrefixQuasiErgodic
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) [CompactSpace U]

/-- Support at a selected-core point in the interior of the prefix forces
any full-process QEM to equal the actual selected prefix probability. -/
theorem full_QEM_eq_prefix_product_of_support
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
      (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ))
    (ν : Measure X) (hq : C.IsQuasiErgodic ν)
    (p : U) (hp : p.val ∈ ν.support) (hpU : p.val ∈ interior U)
    (hppos : 0 < d.eigenvector p) :
    ν = (productMeasure (chain C U hU) (strongFeller C hSF U hU) d).map Subtype.val := by
  let g := ambientVector C hSF U hU d
  let B := interior U ∩ {x | 0 < g x}
  have hBopen : IsOpen B := isOpen_interior.inter (isOpen_lt continuous_const g.continuous)
  have hpB : p.val ∈ B := by
    refine ⟨hpU, ?_⟩
    change 0 < ambientVector C hSF U hU d p.val
    rw [ambientVector_coe C hSF U hU d p]
    exact hppos
  have hBpos : 0 < ν B := by
    apply (Measure.mem_support_iff_forall p.val).mp hp
    exact hBopen.mem_nhds hpB
  have hB : ν B ≠ 0 := ne_of_gt hBpos
  have hqp := productMeasure_isQuasiErgodic (chain C U hU) (strongFeller C hSF U hU) d
  have hqfull := full_process_isQuasiErgodic_of_prefix C U hU hsupport _ hqp
  let : IsProbabilityMeasure ((productMeasure (chain C U hU)
    (strongFeller C hSF U hU) d).map Subtype.val) := hqfull.1
  apply QuasiErgodic.eq_of_positive_basin C _ B _ ν hq hB
  intro f x hx
  have hxU : x ∈ U := interior_subset hx.1
  have hxpos : 0 < d.eigenvector ⟨x, hxU⟩ := by
    rw [← ambientVector_coe C hSF U hU d ⟨x, hxU⟩]
    exact hx.2
  exact full_process_limit_from_prefix C U hU hsupport (strongFeller C hSF U hU) d
    f f.continuous.measurable ⟨‖f‖, f.norm_coe_le_norm⟩ ⟨x, hxU⟩ hxpos

end ConditionedStochasticStabilityHyperbolic.Global.PrefixUniqueness
