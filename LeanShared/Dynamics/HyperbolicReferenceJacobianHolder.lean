module

public import LeanShared.Dynamics.HyperbolicCoreProjectionHolder
public import LeanShared.Dynamics.HyperbolicReferenceCoordinateRatio
public import LeanShared.Geometry.FractionalNativeVectorDerivativeHolder
public import LeanShared.Geometry.NativeChartVectorInjective
public import LeanShared.Geometry.MovingKernelLogJacobianHolder
public import LeanShared.Geometry.BoundedRiemannianDiameter
public import LeanShared.Geometry.SmoothFractionalRegularity
public import LeanShared.Geometry.FractionalManifoldCompositionOne
public import LeanShared.Analysis.RealHolderContinuity
public import LeanShared.Analysis.CompactLocalHolder

/-! The actual unstable logarithmic Jacobian in a smooth immersion reference
metric is Hölder on the core. The splitting, coordinate derivatives, local
frames, Gram logarithms and uniform constant are all proved from literal
hyperbolicity and actual fractional differentiability. The original
continuous Riemannian metric is not assumed smooth. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle FractionalManifoldRegularity
open scoped Topology Manifold ContDiff Bundle
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 3200000 in
theorem HyperbolicData.exists_reference_log_jacobian_holder (h : HyperbolicData (E := E) T Λ)
    {r : ℝ} (regularity : 1 < r) (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (f : M → F) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) ∞ f)
    (immersion : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ H ≥ 0, ∀ x ∈ Λ, ∀ y ∈ Λ,
      |Real.log (h.referenceUnstableJacobian f x) - Real.log (h.referenceUnstableJacobian f y)| ≤
        H * (@dist M (BoundedRiemannianMetric.metric (E := E)).toDist x y) ^ α := by
  obtain ⟨β, positiveβ, _, centers, patch, facts, cover, CP, nonnegativeCP, projectionHolder⟩ :=
    h.exists_core_projection_holder regularity forwardRegular inverseRegular
  let a := min ((r - 1) / 2) (1 / 2)
  have positiveA : 0 < a := lt_min (by linarith) (by norm_num)
  have smallA : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have lowerA : a + 1 < r := by have := min_le_left ((r - 1) / 2) (1 / 2); dsimp only [a]; linarith
  let α := min β a
  have positiveα : 0 < α := lt_min positiveβ positiveA
  have smallα : α < 1 := (min_le_right _ _).trans_lt smallA
  have forward := forwardRegular.mdifferentiable regularity.le
  have inverse := inverseRegular.mdifferentiable regularity.le
  have differentiable := smooth.mdifferentiable (by simp)
  have regT := FractionalOneJetLowering.regular_one_add positiveA smallA lowerA forwardRegular
  have regF : Regular (E := E) (F := F) (a + 1) f := regular_of_smooth smooth (by positivity)
  have regFT := regF.comp_one_add_manifold positiveA smallA regT
  let P : Λ → M → E →L[ℝ] E := fun i y => h.chartProjection i y
  let A : Λ → M → E →L[ℝ] F := fun i y => NativeChartVectorDerivative.coordinateDifferential (E := E) (f ∘ T) i.val y
  let B : Λ → M → E →L[ℝ] F := fun i y => NativeChartVectorDerivative.coordinateDifferential (E := E) f i.val y
  let J : M → ℝ := fun y => Real.log (h.referenceUnstableJacobian f y)
  have formula (i : Λ) (y : M) (hy : y ∈ Λ) (source : y ∈ patch i) :
      J y = Real.log (MovingKernelLogJacobian.ratio (P i y) (A i y) (B i y)) :=
    congrArg Real.log (h.referenceUnstableJacobian_coordinate_ratio forward f differentiable i y hy ((facts i).2 source))
  have idempotent (i : Λ) (y : M) (hy : y ∈ Λ ∩ patch i) (v : E) :
      P i y (P i y v) = P i y v := by
    have same := h.chartProjection_idempotent i y hy.1 ((facts i).2 hy.2)
    exact congrArg (fun L : E →L[ℝ] E => L v) same
  have immersionFT := NativeChartVectorDerivative.diffeomorphism_comp_injective f differentiable immersion T forward inverse
  have injectiveA (i : Λ) (y : M) (hy : y ∈ Λ ∩ patch i) :
      Function.Injective ((A i y).comp (P i y).ker.subtypeL) :=
    (NativeChartVectorDerivative.coordinateDifferential_injective (f ∘ T) immersionFT i.val y ((facts i).2 hy.2)).comp Subtype.val_injective
  have injectiveB (i : Λ) (y : M) (hy : y ∈ Λ ∩ patch i) :
      Function.Injective ((B i y).comp (P i y).ker.subtypeL) :=
    (NativeChartVectorDerivative.coordinateDifferential_injective f immersion i.val y ((facts i).2 hy.2)).comp Subtype.val_injective
  have compactCore : CompactSpace Λ := isCompact_iff_compactSpace.mp h.compact
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let _ : CompactSpace Λ := compactCore
  have lowerPower (b : ℝ) (lower : α ≤ b) (x y : M) : dist x y ^ b ≤ dist x y ^ α :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg (BoundedRiemannianMetric.dist_le_one x y) positiveα.le lower
  have localBound (x : Λ) (_ : x ∈ (univ : Set Λ)) :
      ∃ W : Set Λ, IsOpen W ∧ x ∈ W ∧ ∃ C ≥ 0,
        ∀ y ∈ W, ∀ z ∈ W, dist (J y.val) (J z.val) ≤ C * dist y z ^ α := by
    obtain ⟨i, selected, inside⟩ := mem_iUnion₂.mp (cover x.property)
    obtain ⟨CA, nonnegativeCA, holderA⟩ := regFT.compact_native_vector_derivative_holder positiveA smallA
      i.val (patch i) (facts i).1 (facts i).2
    obtain ⟨CB, nonnegativeCB, holderB⟩ := regF.compact_native_vector_derivative_holder positiveA smallA
      i.val (patch i) (facts i).1 (facts i).2
    let S := Λ ∩ patch i
    have holderP' : ∀ y ∈ S, ∀ z ∈ S, ‖P i y - P i z‖ ≤ CP * dist y z ^ α := by
      intro y hy z hz
      exact (projectionHolder i selected y hy.1 z hz.1 hy.2 hz.2).trans
        (mul_le_mul_of_nonneg_left (lowerPower β (min_le_left _ _) y z) nonnegativeCP)
    have holderA' : ∀ y ∈ S, ∀ z ∈ S, ‖A i y - A i z‖ ≤ CA * dist y z ^ α := by
      intro y hy z hz
      exact (holderA y hy.2 z hz.2).trans
        (mul_le_mul_of_nonneg_left (lowerPower a (min_le_right _ _) y z) nonnegativeCA)
    have holderB' : ∀ y ∈ S, ∀ z ∈ S, ‖B i y - B i z‖ ≤ CB * dist y z ^ α := by
      intro y hy z hz
      exact (holderB y hy.2 z hz.2).trans
        (mul_le_mul_of_nonneg_left (lowerPower a (min_le_right _ _) y z) nonnegativeCB)
    have continuousP := RealHolderContinuity.continuousOn S (P i) α CP positiveα holderP'
    have continuousA := RealHolderContinuity.continuousOn S (A i) α CA positiveα holderA'
    have continuousB := RealHolderContinuity.continuousOn S (B i) α CB positiveα holderB'
    have sourceX : x.val ∈ S := ⟨x.property, interior_subset inside⟩
    obtain ⟨U, openU, memberU, C, nonnegativeC, estimate⟩ :=
      MovingKernelLogJacobian.exists_local_holder S x.val sourceX (P i) (A i) (B i)
        (continuousP x sourceX) (continuousA x sourceX) (continuousB x sourceX)
        (idempotent i) (injectiveA i) (injectiveB i) α CP CA CB nonnegativeCP nonnegativeCA nonnegativeCB
        holderP' holderA' holderB'
    let W : Set Λ := Subtype.val ⁻¹' (U ∩ interior (patch i))
    refine ⟨W, (openU.inter isOpen_interior).preimage continuous_subtype_val, ⟨memberU, inside⟩,
      C, nonnegativeC, ?_⟩
    intro y hy z hz
    have sourceY : y.val ∈ S ∩ U := ⟨⟨y.property, interior_subset hy.2⟩, hy.1⟩
    have sourceZ : z.val ∈ S ∩ U := ⟨⟨z.property, interior_subset hz.2⟩, hz.1⟩
    rw [Real.dist_eq, formula i y.val y.property sourceY.1.2, formula i z.val z.property sourceZ.1.2]
    exact estimate y.val sourceY z.val sourceZ
  obtain ⟨H, nonnegativeH, bound⟩ := CompactLocalHolder.bound_on_compact positiveα smallα.le
    (K := (univ : Set Λ)) isCompact_univ (fun x : Λ => J x.val) localBound
  refine ⟨α, positiveα, smallα, H, nonnegativeH, ?_⟩
  intro x hx y hy
  have estimate := bound ⟨x, hx⟩ (mem_univ _) ⟨y, hy⟩ (mem_univ _)
  simpa only [Real.dist_eq, J, Subtype.dist_eq] using estimate

end LeanShared.HyperbolicBasicSet
