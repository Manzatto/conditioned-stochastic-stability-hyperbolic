module
public import LeanShared.Geometry.CenteredAtlasMisalignedCoordinates
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import LeanShared.Dynamics.HyperbolicIsometricFraming
public import LeanShared.Dynamics.HyperbolicTangentBlockEquivalences

/-! Exact centered chart derivatives along an orbit of a hyperbolic set. In arbitrary
smooth-atlas charts, normalized by the chart differential composed with the Euclidean
splitting frames, the centered representative of a map `H` at an exact orbit pair
`H x = y` has derivative `frame(y)⁻¹ ∘ DH_x ∘ frame(x)` at the origin. For an iterate with
invariant stable/unstable blocks this is the split map `A × B` of the framed blocks. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
open LeanShared.CenteredManifoldCoordinates LeanShared.HyperbolicBasicSet
namespace LeanShared.PeriodicChartDerivative

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

/-- The chart normalization of the Euclidean splitting frame at a point of `Λ`. -/
@[expose] def normalization (a : IsometricFraming h) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (x : Λ) (inside : x.val ∈ c.source) :
    (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) ≃L[ℝ] E :=
  ((a.whole x).trans ((CompactRiemannianChartBounds.chart_differentiable c hc).mfderiv inside)).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x.val))

/-- The exact centered derivative at an orbit pair. -/
theorem exact_derivative (a : IsometricFraming h) (H : M → M) (x y : Λ)
    (orbit : H x.val = y.val) (c c' : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hc' : c' ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (inside : x.val ∈ c.source) (target : y.val ∈ c'.source)
    (smooth : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val) :
    HasFDerivAt (centered (normalization a c hc x inside) (normalization a c' hc' y target)
        (c x.val) (c' y.val) (fun z => c' (H (c.symm z))))
      ((a.whole y).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap)) 0 := by
  obtain ⟨yv, hyv⟩ := y
  change H x.val = yv at orbit
  subst orbit
  have hd := CompactRiemannianChartBounds.chart_differentiable c' hc'
  have raw := CenteredAtlasCoordinates.hasFDerivAt_misaligned_target H x.val (H x.val) c c'
    (CompactRiemannianChartBounds.chart_differentiable c hc) hd inside target target
    (a.whole x) (a.whole ⟨H x.val, hyv⟩) smooth
  refine raw.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  exact (hd.mfderiv target).symm_apply_apply _

/-- At an exact orbit pair the framed derivative of an iterate is the split map of its
framed unstable and stable blocks. -/
theorem framed_blocks (a : IsometricFraming h) (H : M → M) (x y : Λ) (orbit : H x.val = y.val)
    (S : h.stable x.val ≃L[ℝ] h.stable (H x.val)) (U : h.unstable x.val ≃L[ℝ] h.unstable (H x.val))
    (stableAction : ∀ v, (S v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val v.val)
    (unstableAction : ∀ v, (U v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val v.val) :
    ∃ A : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension),
    ∃ B : EuclideanSpace ℝ (Fin a.stableDimension) →L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
      ‖A.symm.toContinuousLinearMap‖ ≤ ‖U.symm.toContinuousLinearMap‖ ∧
      ‖B‖ ≤ ‖S.toContinuousLinearMap‖ ∧
      (a.whole y).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
        (A : _ →L[ℝ] _).prodMap B := by
  obtain ⟨yv, hyv⟩ := y
  change H x.val = yv at orbit
  subst orbit
  set y : Λ := ⟨H x.val, hyv⟩
  let A := ((a.unstable x).toContinuousLinearEquiv.trans U).trans
    (a.unstable y).symm.toContinuousLinearEquiv
  let B := (a.stable y).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (S.toContinuousLinearMap.comp (a.stable x).toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · change ‖((a.unstable x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (U.symm.toContinuousLinearMap.comp
        (a.unstable y).toContinuousLinearEquiv.toContinuousLinearMap))‖ ≤ _
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(a.unstable x).symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      (a.unstable x).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    have h2 : ‖(a.unstable y).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      (a.unstable y).toLinearIsometry.norm_toContinuousLinearMap_le
    calc _ ≤ 1 * (‖U.symm.toContinuousLinearMap‖ * 1) :=
          mul_le_mul h1 ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left h2 (ContinuousLinearMap.opNorm_nonneg _))) (by positivity) zero_le_one
      _ = _ := by ring
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(a.stable y).symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      (a.stable y).symm.toLinearIsometry.norm_toContinuousLinearMap_le
    have h2 : ‖(a.stable x).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
      (a.stable x).toLinearIsometry.norm_toContinuousLinearMap_le
    calc _ ≤ 1 * (‖S.toContinuousLinearMap‖ * 1) :=
          mul_le_mul h1 ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left h2 (ContinuousLinearMap.opNorm_nonneg _))) (by positivity) zero_le_one
      _ = _ := by ring
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, IsometricFraming.whole_apply,
      map_add, ← stableAction, ← unstableAction]
    rw [ContinuousLinearEquiv.symm_apply_eq, IsometricFraming.whole_apply]
    simp only [ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd, A, B,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]

end LeanShared.PeriodicChartDerivative
