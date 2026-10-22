module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHalfConePrincipalJacobian
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafPrincipalKernelBound
public import LeanShared.Analysis.GraphJacobianBounds

/-! The intrinsic unstable Jacobian feeds the actual physical principal row. The prefactor uses only
the fixed Fourier kernels, the dimension and a uniform endpoint-projection bound. The
weight/Jacobian ratio stays joint; neither a tangent-Jacobian source nor a word-length
derivative bound is used. -/

public noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def halfConePrincipalConstant (d : ℕ) (K : ℝ) : ℝ≥0 :=
  ⟨GraphJacobian.densityBound (ι := Fin d) 2 *
    GraphJacobian.densityBound (ι := Fin d) 9 *
    (GraphJacobian.densityBound (ι := Fin d) K *
      GraphJacobian.densityBound (ι := Fin d) (8/3)),
    mul_nonneg (mul_nonneg (GraphJacobian.densityBound_nonneg _)
      (GraphJacobian.densityBound_nonneg _))
      (mul_nonneg (GraphJacobian.densityBound_nonneg _)
        (GraphJacobian.densityBound_nonneg _))⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem C1Embedded.principal_jacobian_of_half_cone_uniform
    {V : Submodule ℝ E} {Γ : Set E} (embedded : C1Embedded V Γ)
    (positive : 0 < Module.finrank ℝ Vᗮ)
    (fake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone V.starProjection (1/2))
      (Module.finrank ℝ Vᗮ) Γ = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (sourceSlope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Vᗮ.starProjection (x-y)‖ ≤ L * ‖V.starProjection (x-y)‖)
    (u : V) (hu : u ∈ FakeLeafGraph.parameterDomain V Γ)
    (U S : Submodule ℝ E) (A : E ≃L[ℝ] E) (Q : E →L[ℝ] U)
    (close : ‖V.starProjection-U.starProjection‖ ≤ (1/8:ℝ))
    (unstableDimension : Module.finrank ℝ V = Module.finrank ℝ U)
    (stableDimension : Module.finrank ℝ S = Module.finrank ℝ Uᗮ)
    (stable : ∀ v : S, Q (A v) = 0)
    (stableSlope : ∀ v : S,
      ‖V.starProjection (v:E)‖ ≤ (1/8:ℝ) * ‖Vᗮ.starProjection (v:E)‖)
    (imageSlope : ∀ v : U,
      ‖Vᗮ.starProjection (A v)‖ ≤ (1/8:ℝ) * ‖V.starProjection (A v)‖)
    (targetProjection : ∀ v : E,
      ‖V.starProjection v‖ ≤ ‖Q v‖ + (1/8:ℝ) * ‖v‖)
    {K : ℝ} (projectionBound : ‖Q‖ ≤ K) :
    let graph := ConeGraphGeometry.graphPoint V
      (FakeLeafGraph.heightExtension V Γ hL sourceSlope)
    (A.toLinearMap.domRestrict U).normDet ≤
      (halfConePrincipalConstant (Module.finrank ℝ V) K : ℝ) *
        (A.toLinearMap.domRestrict (fderiv ℝ graph u).toLinearMap.range).normDet := by
  intro graph
  have actual := embedded.principal_jacobian_of_half_cone positive fake hL sourceSlope u hu
    U S A Q close unstableDimension stableDimension stable stableSlope imageSlope targetProjection
  have bound := GraphJacobian.densityBound_mono (ι := Fin (Module.finrank ℝ U))
    (norm_nonneg Q) projectionBound
  have coefficient :
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) 2 *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) 9 *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (8/3)) ≤
      (halfConePrincipalConstant (Module.finrank ℝ V) K : ℝ) := by
    rw [unstableDimension]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right bound (GraphJacobian.densityBound_nonneg _))
      (mul_nonneg (GraphJacobian.densityBound_nonneg _)
        (GraphJacobian.densityBound_nonneg _))
  exact actual.trans (mul_le_mul_of_nonneg_right coefficient (LinearMap.normDet_nonneg _))

/-- A uniformly controlled endpoint geometry converts an intrinsic
weight/unstable-Jacobian cost directly into a physical Fourier row. -/
theorem exists_half_cone_principal_kernel_bound
    {I : Type*} [Fintype I] (low high : I → 𝓢(E,ℂ))
    (V : Submodule ℝ E) (K : ℝ) :
    ∃ A : ℝ≥0, ∀ (D : Set E)
      (_sourceCone : ConeData V (ProjectionConeTransversality.cone V.starProjection (1/2)))
      (_targetCone : ConeData V D)
      (μ : Measure V) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E),
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target → Measurable F →
      ∀ O : Set E, IsOpen O → O ⊆ F.source →
      (∀ Γ : Index V (ProjectionConeTransversality.cone V.starProjection (1/2)),
        Γ.val ⊆ O → ∃ image : Index V D, image.val = F '' Γ.val) →
      ∀ (U S : E → Submodule ℝ E) (differential : E → E ≃L[ℝ] E)
        (Q : (x : E) → E →L[ℝ] U x),
      (∀ x ∈ O, fderiv ℝ F x = (differential x).toContinuousLinearMap) →
      (∀ x ∈ O, ‖V.starProjection-(U x).starProjection‖ ≤ (1/8:ℝ)) →
      (∀ x ∈ O, Module.finrank ℝ V = Module.finrank ℝ (U x)) →
      (∀ x ∈ O, Module.finrank ℝ (S x) = Module.finrank ℝ (U x)ᗮ) →
      (∀ x ∈ O, ∀ v : S x, Q x (differential x v) = 0) →
      (∀ x ∈ O, ∀ v : S x,
        ‖V.starProjection (v:E)‖ ≤ (1/8:ℝ)*‖Vᗮ.starProjection (v:E)‖) →
      (∀ x ∈ O, ∀ v : U x,
        ‖Vᗮ.starProjection (differential x v)‖ ≤
          (1/8:ℝ)*‖V.starProjection (differential x v)‖) →
      (∀ x ∈ O, ∀ v : E,
        ‖V.starProjection v‖ ≤ ‖Q x v‖+(1/8:ℝ)*‖v‖) →
      (∀ x ∈ O, ‖Q x‖ ≤ K) →
      ∀ g u : E → ℂ, Measurable g → Measurable u → (∀ x ∉ O, g x = 0) →
      ∀ cost : ℝ≥0, ∀ B : ℝ≥0∞,
      (∀ Δ : Index V D,
        ∫⁻ y, ‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume V μ Δ.val ≤ B) →
      (∀ x ∈ O, ‖g x‖ₑ ≤ (cost : ℝ≥0∞) *
        ENNReal.ofReal (((differential x).toLinearMap.domRestrict (U x)).normDet)) →
      ∀ j : ℕ × I, ∀ Γ : Index V
        (ProjectionConeTransversality.cone V.starProjection (1/2)),
      (∫⁻ x, ‖∫ w, DyadicSymbols.kernel low high j (x-w)*g w*u (F w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume V μ Γ.val) ≤
          (A : ℝ≥0∞) * ((cost : ℝ≥0∞)*B) := by
  obtain ⟨fourier, rows⟩ := exists_principal_kernel_bound low high
  let endpoint := halfConePrincipalConstant (Module.finrank ℝ V) K
  refine ⟨fourier * endpoint, ?_⟩
  intro D sourceCone targetCone μ _ F forward backward measurableF O openO inside images
    U S differential Q derivative close unstableDimension stableDimension stable stableSlope
    imageSlope targetProjection projectionBound g u measurableG measurableU supported cost B leafBound intrinsic
  have tangent : ∀ Γ : Index V
      (ProjectionConeTransversality.cone V.starProjection (1/2)), Γ.val ⊆ O →
      let graph := ConeGraphGeometry.graphPoint V (FakeLeafGraph.heightExtension V Γ.val
        (slope_positive V _ sourceCone).le (slope_bound V _ sourceCone Γ));
      ∀ v ∈ FakeLeafGraph.parameterDomain V Γ.val, ‖g (graph v)‖ₑ ≤
        ((endpoint * cost : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (((fderiv ℝ F (graph v)).toLinearMap.domRestrict
            (fderiv ℝ graph v).toLinearMap.range).normDet) := by
    intro Γ subset graph v hv
    have member : graph v ∈ O := subset
      ((FakeLeafGraph.graphExtension_image V Γ.val
        (slope_positive V _ sourceCone).le (slope_bound V _ sourceCone Γ)).subset ⟨v,hv,rfl⟩)
    have jacobian := Γ.property.1.principal_jacobian_of_half_cone_uniform
      sourceCone.stable_positive Γ.property.2 (slope_positive V _ sourceCone).le
      (slope_bound V _ sourceCone Γ) v hv (U (graph v)) (S (graph v))
      (differential (graph v)) (Q (graph v)) (close _ member)
      (unstableDimension _ member) (stableDimension _ member) (stable _ member)
      (stableSlope _ member) (imageSlope _ member) (targetProjection _ member)
      (projectionBound _ member)
    have estimate := (intrinsic _ member).trans
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal jacobian) bot_le)
    change ‖g (graph v)‖ₑ ≤ (cost : ℝ≥0∞) * ENNReal.ofReal
      ((endpoint : ℝ) * (((differential (graph v)).toLinearMap.domRestrict
        (fderiv ℝ graph v).toLinearMap.range).normDet)) at estimate
    have castProduct (z : ℝ) : ENNReal.ofReal ((endpoint : ℝ) * z) =
        (endpoint : ℝ≥0∞) * ENNReal.ofReal z := by
      exact (ENNReal.ofReal_mul (show (0:ℝ) ≤ (endpoint:ℝ) from endpoint.property)).trans
        (congrArg (fun c : ℝ≥0∞ => c * ENNReal.ofReal z) (ENNReal.coe_nnreal_eq endpoint).symm)
    rw [castProduct] at estimate
    have linearDerivative : (differential (graph v)).toLinearMap =
        (fderiv ℝ F (graph v)).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap (derivative _ member).symm
    rw [linearDerivative] at estimate
    simpa only [ENNReal.coe_mul, mul_assoc, mul_comm, mul_left_comm] using estimate
  intro j Γ
  have estimate := rows V _ D sourceCone targetCone μ F forward backward measurableF O openO
    inside images g u measurableG measurableU supported (endpoint*cost) B leafBound tangent j Γ
  simpa only [ENNReal.coe_mul, mul_assoc] using estimate

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
