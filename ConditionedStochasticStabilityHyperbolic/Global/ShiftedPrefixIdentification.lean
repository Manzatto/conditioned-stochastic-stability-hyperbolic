module

public import ConditionedStochasticStabilityHyperbolic.Global.PrefixUniqueness

/-! # Shifting the selected filtration leaves the full-process QEM unchanged

Both prefix products are constructed from their produced spectral data. The
second prefix may be enlarged to contain a prescribed stable starting state.
Common selected-core support and original interior positivity identify their
full-process measures, while the absorbing set and original process stay fixed.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ShiftedPrefixIdentification
open AbsorbingMarkovChains ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
open PrefixQuasiErgodic PrefixUniqueness PrefixCorrespondence
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
  [CompactSpace U] [CompactSpace V]
  (hsU : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
  (hsV : ∀ x ∈ V, C.killedTransition x Vᶜ = 0)
  (dU : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
    (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ))
  (dV : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C V hV)
    (strongFeller C hSF V hV)) (1 : V →ᵇ ℝ))

include hsU hsV in
/-- Actual produced prefix products coincide at a common selected-core point;
no full-process QEM or uniqueness conclusion is supplied. -/
theorem actual_prefix_products_eq
    (p : U) (hpU : p.val ∈ interior U) (hp : 0 < dU.eigenvector p)
    (hpV : p.val ∈ ((productMeasure (chain C V hV) (strongFeller C hSF V hV) dV).map
      Subtype.val).support) :
    (productMeasure (chain C V hV) (strongFeller C hSF V hV) dV).map Subtype.val =
      (productMeasure (chain C U hU) (strongFeller C hSF U hU) dU).map Subtype.val := by
  have hqV := full_process_isQuasiErgodic_of_prefix C V hV hsV _
    (productMeasure_isQuasiErgodic (chain C V hV) (strongFeller C hSF V hV) dV)
  exact full_QEM_eq_prefix_product_of_support C hSF U hU hsU dU _ hqV p hpV hpU hp

include hsU hsV in
/-- Conditioned statistics from an enlarged/shifted prefix converge to the
original selected probability once genuine control positivity is established. -/
theorem full_limit_to_original_selected_product
    (p : U) (hpU : p.val ∈ interior U) (hp : 0 < dU.eigenvector p)
    (hpV : p.val ∈ ((productMeasure (chain C V hV) (strongFeller C hSF V hV) dV).map
      Subtype.val).support)
    (x : V) (hx : 0 < dV.eigenvector x)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
      (𝓝 (∫ y, f y ∂(productMeasure (chain C U hU) (strongFeller C hSF U hU) dU).map
        Subtype.val)) := by
  have hlim := full_process_limit_from_prefix C V hV hsV (strongFeller C hSF V hV) dV f hf hb x hx
  rw [actual_prefix_products_eq C hSF U V hU hV hsU hsV dU dV p hpU hp hpV] at hlim
  exact hlim

end ConditionedStochasticStabilityHyperbolic.Global.ShiftedPrefixIdentification
