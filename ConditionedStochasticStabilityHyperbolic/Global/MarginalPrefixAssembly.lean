module

public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies

/-! Assembly from the exact first marginal produced by stabilized-prefix
spectral descent. Core support and the base-family identity are transported,
rather than imposed again on the original system. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.MarginalPrefixAssembly
open LeanShared ComplexStrongFeller LayerQuasiErgodic DerivedHG2Application
open AssembleShiftedPrefixFamilies FiltrationPressureConfinement ShiftedFiltrationGeometry ActualFiltrationGrowth

 theorem fst_support {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X]
    [OpensMeasurableSpace Y] (μ : Measure (X × Y)) (x : X) (y : Y)
    (h : (x, y) ∈ μ.support) : x ∈ (μ.map Prod.fst).support := by
  rw [Measure.support_eq_forall_isOpen] at h ⊢
  intro U hx hU
  rw [Measure.map_apply measurable_fst hU.measurableSet]
  exact h (Prod.fst ⁻¹' U) hx (hU.preimage continuous_fst)

variable {X Y I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))

local instance compactPrefix (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D
    ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))

omit [CompactSpace X] in
 theorem assemble_at
    (closedProduct : ∀ s, NNReal → Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε)
    (dp : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
      (RestrictedLayerChain.strongFeller (C ε) (sf ε hε)
        (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))))
      (1 : actualPrefix T A Λ ℓ D (terminal s) N →ᵇ ℝ))
    (invariant : ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) N,
      (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) N)ᶜ = 0)
    (positive : ∀ x : actualPrefix T A Λ ℓ D (terminal s) N,
      x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s)) → 0 < dp.eigenvector x)
    (productAmbient : Measure (X × Y))
    (marginal : (productMeasure _ _ dp).map Subtype.val = productAmbient.map Prod.fst)
    (support : Λ (D.index (selectedIndex ℓ t terminal root s)) ×ˢ univ ⊆ productAmbient.support)
    (base_identity : N = 0 → productAmbient.map Prod.fst = (closedProduct s ε).map Subtype.val)
    (y : Y) : Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
  refine ⟨{ data := dp, invariant := invariant, positive := positive, support := ?_, base_identity := ?_ }⟩
  · intro x hx
    rw [marginal]
    exact fst_support productAmbient x y (support ⟨hx, mem_univ y⟩)
  · exact fun hN => marginal.trans (base_identity hN)

end ConditionedStochasticStabilityHyperbolic.Global.MarginalPrefixAssembly
