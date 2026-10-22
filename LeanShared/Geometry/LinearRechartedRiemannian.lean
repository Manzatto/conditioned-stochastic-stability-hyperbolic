module
public import LeanShared.Geometry.LinearRechartedTangent
public import LeanShared.Geometry.CompactRiemannianMetricComparison
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Transport the supplied tangent metric through the differential of the
actual identity recharting. The transported norm is exactly the old norm
under the fiber equivalence. No ambient model inner product is imposed. -/
public noncomputable section
open Set IsManifold Bundle Bornology
open scoped Manifold ContDiff Topology
namespace LeanShared.LinearRechartedManifold
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : E ≃L[ℝ] F)

/-- The actual old bilinear form, expressed on the new tangent fiber. -/
@[expose] def transportMetric
    (g : RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x)) :
    letI := charts (M := M) e;
    RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,F)) x) := by
  letI := charts (M := M) e
  let j := identityDifferential (M := M) e
  exact {
    inner := fun x => ((j x).arrowCongr ((j x).arrowCongr
      (ContinuousLinearEquiv.refl ℝ ℝ))) (g.inner x)
    symm := fun x v w => g.symm x ((j x).symm v) ((j x).symm w)
    pos := fun x v hv => g.pos x ((j x).symm v) (by
      intro h
      exact hv ((j x).symm.injective (h.trans (map_zero _).symm)))
    continuousAt := fun x => by
      exact ((g.continuousAt x).comp_of_eq (by fun_prop :
        ContinuousAt ((j x).symm : TangentSpace (𝓘(ℝ,F)) x →
          TangentSpace (𝓘(ℝ,E)) x) 0) (map_zero _))
    isVonNBounded := fun x => by
      have bounded := (g.isVonNBounded x).image (j x).toContinuousLinearMap
      convert bounded using 1
      ext v
      constructor
      · intro hv
        exact ⟨(j x).symm v, hv, (j x).apply_symm_apply v⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw }

theorem transportMetric_inner
    (g : RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x)) :
    letI := charts (M := M) e;
    ∀ x (v w : TangentSpace (𝓘(ℝ,F)) x),
      (transportMetric e g).inner x v w =
        g.inner x ((identityDifferential e x).symm v)
          ((identityDifferential e x).symm w) := by
  intro x v w
  simp only [transportMetric, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.refl_apply]


theorem transportMetric_norm
    (g : RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x))
    (x : M) (v : TangentSpace (𝓘(ℝ,E)) x) :
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := ⟨g⟩;
    letI := charts (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e g⟩;
    ‖identityDifferential e x v‖ = ‖v‖ := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := ⟨g⟩
  let := charts (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e g⟩
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  change Real.sqrt ((transportMetric e g).inner x
    (identityDifferential e x v) (identityDifferential e x v)) =
    Real.sqrt (g.inner x v v)
  rw [transportMetric_inner]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- The identity differential is an exact isometry for the transported
supplied metric. -/
@[expose] def identityIsometry
    (g : RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ,E)) x)) (x : M) :
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := ⟨g⟩;
    letI := charts (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e g⟩;
    TangentSpace (𝓘(ℝ,E)) x ≃ₗᵢ[ℝ] TangentSpace (𝓘(ℝ,F)) x := by
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := ⟨g⟩
  letI := charts (M := M) e
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e g⟩
  exact { (identityDifferential e x).toLinearEquiv with
    norm_map' := transportMetric_norm e g x }

variable [IsManifold (𝓘(ℝ,E)) ∞ M] [FiniteDimensional ℝ F]

theorem continuous_transportMetric
    (g : ContinuousRiemannianMetric E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)) :
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    Continuous (fun x => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x
      ((transportMetric e g.toRiemannianMetric).inner x)) := by
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) :=
    ⟨g.toRiemannianMetric⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  rw [continuousAt_clm_apply]
  intro v
  rw [continuousAt_clm_apply]
  intro w
  let t := trivializationAt F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) x₀
  have localVector (u : F) : ContinuousAt
      (fun x => TotalSpace.mk' F x (t.symmL ℝ x u)) x₀ := by
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_id, ?_⟩
    apply (continuousAt_const (y := u)).congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) x₀)]
      with x hx
    change (t ⟨x, t.symmL ℝ x u⟩).2 = u
    rw [Trivialization.symmL_apply t hx, Trivialization.apply_mk_symm t hx]
  have pulled (u : F) : ContinuousAt
      (fun x => TotalSpace.mk' E x
        ((identityDifferential e x).symm (t.symmL ℝ x u))) x₀ :=
    (tangentHomeomorph (M := M) e).symm.continuous.continuousAt.comp (localVector u)
  have pairing := (pulled v).inner_bundle (pulled w)
  apply pairing.congr_of_eventuallyEq
  filter_upwards [t.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) x₀)]
    with x hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    hom_trivializationAt, Trivialization.continuousLinearMapAt_apply]
  rw [Trivialization.coe_linearMapAt_of_mem _ (show x ∈
    ((trivializationAt F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) x₀).continuousLinearMap
      (RingHom.id ℝ) (trivializationAt ℝ (fun _ : M => ℝ) x₀)).baseSet from
      ⟨hx, mem_univ x⟩)]
  simp only [Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, transportMetric_inner]
  simp only [Trivialization.linearMapAt_apply, ite_eq_left (show x ∈
    (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet from mem_univ x)]
  rfl

/-- The transported metric is continuous in the actual recharted tangent
bundle, established from continuity of the original supplied metric. -/
@[expose] def transportContinuousMetric
    (g : ContinuousRiemannianMetric E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)) :
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    ContinuousRiemannianMetric F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) := by
  letI := charts (M := M) e
  letI := manifold (M := M) e
  exact {
    inner := (transportMetric e g.toRiemannianMetric).inner
    symm := (transportMetric e g.toRiemannianMetric).symm
    pos := (transportMetric e g.toRiemannianMetric).pos
    isVonNBounded := (transportMetric e g.toRiemannianMetric).isVonNBounded
    continuous := continuous_transportMetric e g }

end LeanShared.LinearRechartedManifold
