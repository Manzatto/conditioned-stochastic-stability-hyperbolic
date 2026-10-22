module
public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry

/-! The original selected removed boundary has zero PRODUCT reference volume,
including the first stratum where equality eliminates the boundary outright. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.ProductSelectedBoundary
open ShiftedFiltrationGeometry FiltrationPressureConfinement

theorem removed_product_null
    {X Y I : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X) (hA : IsOpen A)
    (Λ : I → Set X) (ell : ℕ) (D : AdaptedSource T A Λ ell)
    (σ : Measure (X × Y))
    (preimage : ∀ B, σ B = 0 → σ ((T.prodCongr S) ⁻¹' B) = 0)
    (null : ∀ i, 0 < i → i ≤ ell →
      σ (frontier ((ProductAdaptedFiltration.source T S A Λ ell D).levels i)) = 0)
    (j : Fin ell) :
    σ ((closedLayer T A Λ ell 0 D j \ stratum T A Λ ell 0 D j) ×ˢ (univ : Set Y)) = 0 := by
  have zero := ShiftedBoundaryGeometry.closed_layer_extra_zero (T.prodCongr S)
    (A ×ˢ (univ : Set Y)) (hA.prod isOpen_univ) (fun i => Λ i ×ˢ univ) ell 0
    (ProductAdaptedFiltration.source T S A Λ ell D) σ preimage null j
  change σ (closedLayer (T.prodCongr S) (A ×ˢ (univ : Set Y))
    (fun i => Λ i ×ˢ univ) ell 0 (ProductAdaptedFiltration.source T S A Λ ell D) j \
    stratum (T.prodCongr S) (A ×ˢ (univ : Set Y)) (fun i => Λ i ×ˢ univ) ell 0
      (ProductAdaptedFiltration.source T S A Λ ell D) j) = 0 at zero
  rw [ProductAdaptedFiltration.closedLayer_product, ProductAdaptedFiltration.stratum_product] at zero
  convert zero using 1
  congr 1
  ext z
  simp only [mem_sdiff, mem_prod, mem_univ, and_true]
end ConditionedStochasticStabilityHyperbolic.Global.ProductSelectedBoundary
