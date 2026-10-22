module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHalfConePrincipalKernelBound
public import LeanShared.Analysis.NearOrthogonalStableProjection
public import LeanShared.Analysis.PhysicalLocalAmplitudeRows

/-! Actual intrinsic principal rows with their endpoint projection constructed
from the adapted stable projectors. The structural constant depends only on
the fixed multiplier bases and dimension, never on the derivative of a word. -/

public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap BigOperators

namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_intrinsic_principal_kernel_bound
    {I : Type*} [Fintype I] (low high : I → 𝓢(E,ℂ)) (V : Submodule ℝ E) :
    ∃ A : ℝ≥0, ∀ (D : Set E)
      (_sourceCone : ConeData V (ProjectionConeTransversality.cone V.starProjection (1/2)))
      (_targetCone : ConeData V D)
      (μ : Measure V) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E),
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target → Measurable F →
      ∀ O : Set E, IsOpen O → O ⊆ F.source →
      (∀ Γ : Index V (ProjectionConeTransversality.cone V.starProjection (1/2)),
        Γ.val ⊆ O → ∃ image : Index V D, image.val = F '' Γ.val) →
      ∀ (source target : E → E →L[ℝ] E) (differential : E → E ≃L[ℝ] E),
      (∀ x ∈ O, fderiv ℝ F x = (differential x).toContinuousLinearMap) →
      (∀ x ∈ O, ‖source x-Vᗮ.starProjection‖ ≤ (1/64:ℝ)) →
      (∀ x ∈ O, ‖target x-Vᗮ.starProjection‖ ≤ (1/64:ℝ)) →
      (∀ x ∈ O, Module.finrank ℝ (source x).ker = Module.finrank ℝ V) →
      (∀ x ∈ O, Module.finrank ℝ (target x).range = Module.finrank ℝ Vᗮ) →
      (∀ x ∈ O, ∀ v, target x (target x v) = target x v) →
      (∀ x ∈ O, ∀ v : (target x).range.comap (differential x).toLinearMap,
        ‖V.starProjection (v:E)‖ ≤ (1/8:ℝ)*‖Vᗮ.starProjection (v:E)‖) →
      (∀ x ∈ O, ∀ v : (source x).ker,
        ‖Vᗮ.starProjection (differential x v)‖ ≤
          (1/8:ℝ)*‖V.starProjection (differential x v)‖) →
      ∀ g u : E → ℂ, Measurable g → Measurable u → (∀ x ∉ O, g x = 0) →
      ∀ cost : ℝ≥0, ∀ B : ℝ≥0∞,
      (∀ Δ : Index V D,
        ∫⁻ y, ‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume V μ Δ.val ≤ B) →
      (∀ x ∈ O, ‖g x‖ₑ ≤ (cost : ℝ≥0∞) *
        ENNReal.ofReal (((differential x).toLinearMap.domRestrict (source x).ker).normDet)) →
      ∀ j : ℕ × I, ∀ Γ : Index V
        (ProjectionConeTransversality.cone V.starProjection (1/2)),
      (∫⁻ x, ‖∫ w, DyadicSymbols.kernel low high j (x-w)*g w*u (F w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume V μ Γ.val) ≤
          (A : ℝ≥0∞) * ((cost : ℝ≥0∞)*B) := by
  obtain ⟨A, rows⟩ := exists_half_cone_principal_kernel_bound low high V 2
  refine ⟨A, ?_⟩
  intro D sourceCone targetCone μ _ F forward backward measurableF O openO inside images
    source target differential derivative sourceClose targetClose sourceDimension targetDimension
    idempotent stableSlope imageSlope g u measurableG measurableU supported cost B leafBound intrinsic
  let U := fun x => (source x).ker
  let S := fun x => (target x).range.comap (differential x).toLinearMap
  let Q := fun x => ProjectedEndpointMap.map (U x) (ContinuousLinearMap.id ℝ E-target x)
  have kernelClose (x : E) (hx : x ∈ O) :
      ‖V.starProjection-(U x).starProjection‖ ≤ (1/16:ℝ) :=
    NearOrthogonalStableProjection.kernel_close V (source x) (sourceDimension x hx) (sourceClose x hx)
  have projection (x : E) (hx : x ∈ O) :
      ‖Q x‖ ≤ 2 ∧ ∀ v : E, ‖V.starProjection v‖ ≤ ‖Q x v‖+(1/8:ℝ)*‖v‖ :=
    ProjectedEndpointMap.bounds V (U x) (ContinuousLinearMap.id ℝ E-target x)
      (kernelClose x hx) (NearOrthogonalStableProjection.complement_close V (target x) (targetClose x hx))
  have dimension (x : E) (hx : x ∈ O) :
      Module.finrank ℝ (S x) = Module.finrank ℝ (U x)ᗮ := by
    have complements : Module.finrank ℝ Vᗮ = Module.finrank ℝ (U x)ᗮ := by
      have first := V.finrank_add_finrank_orthogonal
      have second := (U x).finrank_add_finrank_orthogonal
      have same := sourceDimension x hx
      change Module.finrank ℝ (U x) = Module.finrank ℝ V at same
      omega
    change Module.finrank ℝ ((target x).range.comap (differential x).toLinearMap) = _
    rw [Submodule.comap_equiv_eq_map_symm (differential x).toLinearEquiv,
      LinearEquiv.finrank_map_eq]
    exact (targetDimension x hx).trans complements
  have stable (x : E) (hx : x ∈ O) (v : S x) : Q x (differential x v) = 0 := by
    obtain ⟨w, hw⟩ := v.property
    change target x w = differential x v at hw
    have fixed : target x (differential x v) = differential x v := by
      rw [←hw]
      exact idempotent x hx w
    change (U x).orthogonalProjectionOnto (differential x v-target x (differential x v)) = 0
    rw [fixed, sub_self, map_zero]
  exact rows D sourceCone targetCone μ F forward backward measurableF O openO inside images
    U S differential Q derivative
    (fun x hx => (kernelClose x hx).trans (by norm_num))
    (fun x hx => (sourceDimension x hx).symm) dimension stable stableSlope imageSlope
    (fun x hx => (projection x hx).2) (fun x hx => (projection x hx).1)
    g u measurableG measurableU supported cost B leafBound intrinsic

/-- Piecewise itinerary windows retain the exact sum of intrinsic cylinder
costs. The coordinate map is only required to be continuous on its source. -/
theorem exists_intrinsic_principal_cylinder_bound
    {I : Type*} [Fintype I] (low high : I → 𝓢(E,ℂ)) (V : Submodule ℝ E) :
    ∃ A : ℝ≥0, ∀ (D : Set E)
      (_sourceCone : ConeData V (ProjectionConeTransversality.cone V.starProjection (1/2)))
      (_targetCone : ConeData V D)
      (μ : Measure V) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E),
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target → Measurable F →
      ∀ (J : Type) [Fintype J] (O : J → Set E),
      (∀ i, IsOpen (O i)) → (∀ i, O i ⊆ F.source) →
      (∀ i, ∀ Γ : Index V (ProjectionConeTransversality.cone V.starProjection (1/2)),
        Γ.val ⊆ O i → ∃ image : Index V D, image.val = F '' Γ.val) →
      ∀ (source target : E → E →L[ℝ] E) (differential : E → E ≃L[ℝ] E),
      (∀ i, ∀ x ∈ O i, fderiv ℝ F x = (differential x).toContinuousLinearMap) →
      (∀ i, ∀ x ∈ O i, ‖source x-Vᗮ.starProjection‖ ≤ (1/64:ℝ)) →
      (∀ i, ∀ x ∈ O i, ‖target x-Vᗮ.starProjection‖ ≤ (1/64:ℝ)) →
      (∀ i, ∀ x ∈ O i, Module.finrank ℝ (source x).ker = Module.finrank ℝ V) →
      (∀ i, ∀ x ∈ O i, Module.finrank ℝ (target x).range = Module.finrank ℝ Vᗮ) →
      (∀ i, ∀ x ∈ O i, ∀ v, target x (target x v) = target x v) →
      (∀ i, ∀ x ∈ O i, ∀ v : (target x).range.comap (differential x).toLinearMap,
        ‖V.starProjection (v:E)‖ ≤ (1/8:ℝ)*‖Vᗮ.starProjection (v:E)‖) →
      (∀ i, ∀ x ∈ O i, ∀ v : (source x).ker,
        ‖Vᗮ.starProjection (differential x v)‖ ≤
          (1/8:ℝ)*‖V.starProjection (differential x v)‖) →
      ∀ (g u : E → ℂ) (pieces : J → E → ℂ), Continuous u →
      (∀ i, Continuous (pieces i)) → (∀ i, HasCompactSupport (pieces i)) →
      (∀ i, tsupport (pieces i) ⊆ O i) → (∀ x, g x = ∑ i, pieces i x) →
      ∀ cost : J → ℝ≥0, ∀ B : ℝ≥0∞,
      (∀ Δ : Index V D,
        ∫⁻ y, ‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume V μ Δ.val ≤ B) →
      (∀ i, ∀ x ∈ O i, ‖pieces i x‖ₑ ≤ (cost i : ℝ≥0∞) *
        ENNReal.ofReal (((differential x).toLinearMap.domRestrict (source x).ker).normDet)) →
      ∀ j : ℕ × I, ∀ Γ : Index V
        (ProjectionConeTransversality.cone V.starProjection (1/2)),
      (∫⁻ x, ‖∫ w, DyadicSymbols.kernel low high j (x-w)*g w*u (F w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume V μ Γ.val) ≤
          (A : ℝ≥0∞) * ((∑ i, (cost i : ℝ≥0∞))*B) := by
  obtain ⟨A, rows⟩ := exists_intrinsic_principal_kernel_bound low high V
  refine ⟨A, ?_⟩
  intro D sourceCone targetCone μ _ F forward backward measurableF J _ O openO inside images
    source target differential derivative sourceClose targetClose sourceDimension targetDimension
    idempotent stableSlope imageSlope g u pieces continuousU continuousPieces compactPieces
    supported reconstruct cost B leafBound intrinsic j Γ
  apply PhysicalLocalAmplitudeRows.bound_of_cost (DyadicSymbols.kernel low high j) F u
    continuousU g pieces continuousPieces compactPieces (fun i => (supported i).trans (inside i))
    reconstruct (EmbeddedSubmanifoldVolume.volume V μ Γ.val) A B (fun i => (cost i : ℝ≥0∞))
  intro i
  exact rows D sourceCone targetCone μ F forward backward measurableF (O i) (openO i) (inside i)
    (images i) source target differential (derivative i) (sourceClose i) (targetClose i)
    (sourceDimension i) (targetDimension i) (idempotent i) (stableSlope i) (imageSlope i)
    (pieces i) u (continuousPieces i).measurable continuousU.measurable
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (supported i h)))
    (cost i) B leafBound (intrinsic i) j Γ

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
