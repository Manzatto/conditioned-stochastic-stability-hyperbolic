module
public import LeanShared.Geometry.FractionalHolderCharts
public import LeanShared.Geometry.HolderFractionalRegularity
public import LeanShared.Geometry.ChartLocalization
public import LeanShared.Analysis.LocalHolderProduct
public import LeanShared.Analysis.LocalSmoothHolder
public import LeanShared.Analysis.CompactSupportedLocalHolder
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! Genuine chart localization preserves actual fractional regularity
of order in (0,1). Continuity through the chart boundary, the two-point
Hölder constant and compact support are proved from the actual cutoff,
chart and function. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ChartFractionalLocalization
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (θ : M → ℂ)
  (support : tsupport θ ⊆ e.source) (compact : HasCompactSupport θ)

include support compact in
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] in
theorem continuous {f : M → ℂ} (hθ : Continuous θ) (hf : Continuous f) :
    Continuous (ChartLocalization.coordinate e θ f) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ e.target
  · have inverse := e.symm.continuousAt hy
    apply ((hθ.continuousAt.comp inverse).mul (hf.continuousAt.comp inverse)).congr
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact (ite_eq_left hz).symm
  · have outside : y ∉ ChartLocalization.localSupport e θ :=
      fun hn => hy (ChartLocalization.localSupport_subset_target e θ support hn)
    apply continuousAt_const.congr
    filter_upwards [(ChartLocalization.localSupport_isCompact e θ support compact).isClosed.isOpen_compl.mem_nhds outside]
      with z hz
    exact (ChartLocalization.coordinate_zero_outside e θ f z hz).symm

variable (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (hθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  {f : M → ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
  (hf : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a f)

include support compact he hθ ha ha1 hf in
omit [FiniteDimensional ℝ E] in
theorem local_holder (y : E) :
    ∃ W : Set E, IsOpen W ∧ y ∈ W ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v ∈ W, ∀ w ∈ W,
        ‖ChartLocalization.coordinate e θ f v - ChartLocalization.coordinate e θ f w‖ ≤
          C * ‖v-w‖ ^ a := by
  by_cases hy : y ∈ e.target
  · obtain ⟨U, openU, inU, subU, C, hC, boundF⟩ :=
      FractionalManifoldRegularity.local_holder_in_chart ha ha1 hf e he y hy
    let φ := ChartLocalization.coordinate e θ (fun _ => (1 : ℂ))
    have smoothφ : ContDiff ℝ ∞ φ :=
      ChartLocalization.coordinate_contDiff e θ support he hθ compact _ contMDiff_const
    obtain ⟨O, openO, inO, subO, D, hD, boundφ⟩ := LocalSmoothHolder.exists_holder_on
      (smoothφ.contDiffAt.of_le (by simp)) ha1.le (e.open_target.mem_nhds hy)
    obtain ⟨W, openW, inW, subW, A, hA, estimate⟩ :=
      LocalHolderProduct.exists_bound ha.le hD hC (openO.mem_nhds inO) (openU.mem_nhds inU)
        boundφ boundF
    refine ⟨W, openW, inW, A, hA, fun v hv w hw => ?_⟩
    have vtarget := subO (subW hv).1
    have wtarget := subO (subW hw).1
    simpa only [φ, ChartLocalization.coordinate, ite_eq_left vtarget, ite_eq_left wtarget,
      mul_one] using estimate v hv w hw
  · have outside : y ∉ ChartLocalization.localSupport e θ :=
      fun hn => hy (ChartLocalization.localSupport_subset_target e θ support hn)
    refine ⟨(ChartLocalization.localSupport e θ)ᶜ,
      (ChartLocalization.localSupport_isCompact e θ support compact).isClosed.isOpen_compl,
      outside, 0, le_rfl, fun v hv w hw => ?_⟩
    rw [ChartLocalization.coordinate_zero_outside e θ f v hv,
      ChartLocalization.coordinate_zero_outside e θ f w hw]
    simp only [sub_self, norm_zero, zero_mul, le_refl]

@[expose] def bounded : E →ᵇ ℂ :=
  ofCompactSupport (ChartLocalization.coordinate e θ f)
    (continuous e θ support compact hθ.continuous hf.differentiable.continuous)
    (ChartLocalization.coordinate_hasCompactSupport e θ support compact f)

include he ha ha1 in
theorem global_holder : ∃ C : ℝ, 0 ≤ C ∧ ∀ v w,
    ‖bounded e θ support compact hθ hf v - bounded e θ support compact hθ hf w‖ ≤
      C * ‖v-w‖ ^ a := by
  simpa only [dist_eq_norm] using CompactSupportedLocalHolder.exists_bound
    (bounded e θ support compact hθ hf)
    (ChartLocalization.coordinate_hasCompactSupport e θ support compact f) ha ha1.le
    (fun y => by
      change ∃ W : Set E, IsOpen W ∧ y ∈ W ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ v ∈ W, ∀ w ∈ W,
          ‖ChartLocalization.coordinate e θ f v - ChartLocalization.coordinate e θ f w‖ ≤
            C * dist v w ^ a
      simpa only [dist_eq_norm] using local_holder e θ support compact he hθ ha ha1 hf y)

include support compact he hθ ha ha1 hf in
theorem regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
    (ChartLocalization.coordinate e θ f) := by
  obtain ⟨C, hC, bound⟩ := global_holder e θ support compact he hθ ha ha1 hf
  exact FractionalManifoldRegularity.regular_of_holder ha ha1
    (continuous e θ support compact hθ.continuous hf.differentiable.continuous) hC bound
end LeanShared.ChartFractionalLocalization
