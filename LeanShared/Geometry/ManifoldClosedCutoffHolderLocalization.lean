module
public import LeanShared.Geometry.ManifoldHolderCutoffLocalization
public import LeanShared.Geometry.CompactSchwartzHolderNormedCore

/-! Any genuine chart and supported smooth cutoff localizes the actual
global little Holder quotient into the little Holder core on that exact
closed compact support. The target support need not be open, and need not
be one of the global quotient's own selected chart cutoffs. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldClosedCutoffHolderLocalization
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source)

abbrev Global := ManifoldSmoothHolderCore.Lower e D openV hb hb1
abbrev Local := EuclideanSmoothHolderCore.space
  (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
local instance globalNormed : NormedAddCommGroup (Global e D openV hb hb1) := inferInstance
local instance globalSemi : SeminormedAddCommGroup (Global e D openV hb hb1) :=
  (globalNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance globalScalar : NormedSpace ℂ (Global e D openV hb hb1) := inferInstance
local instance localNormed : NormedAddCommGroup (Local hb hb1 c θ compactθ supportθ) := inferInstance
local instance localSemi : SeminormedAddCommGroup (Local hb hb1 c θ compactθ supportθ) :=
  (localNormed hb hb1 c θ compactθ supportθ).toSeminormedAddCommGroup
local instance localScalar : NormedSpace ℂ (Local hb hb1 c θ compactθ supportθ) := inferInstance

@[expose] def core : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    Local hb hb1 c θ compactθ supportθ :=
  (CompactSchwartzHolderNormedCore.core
    (ChartLocalization.localSupport_isCompact c θ supportθ compactθ) hb hb1).comp
    (ChartLocalization.linearMap c θ supportθ hc smoothθ
      (SmoothSupportedManifoldCore.functions V) (fun v => v.property.1) compactθ)

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem core_graph (region : V ⊆ S) (v : SmoothSupportedManifoldCore.core (E := E) V) :
    (core hb hb1 c hc θ smoothθ compactθ supportθ v).val =
      ManifoldHolderCutoffLocalization.localization e D atlas openV hb hb1
        c hc θ smoothθ compactθ supportθ (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 v) := by
  apply BoundedHolderSpace.physical_injective E b
  ext y
  change EuclideanSmoothHolderCore.physical
    (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
      (core hb hb1 c hc θ smoothθ compactθ supportθ v) y = _
  rw [ManifoldHolderCutoffLocalization.physical_localization]
  have represented : (ManifoldSmoothHolderCore.physical e D openV hb hb1
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 v) : M → ℂ) = v.val := by
    funext x
    exact ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region v x
  rw [represented]
  rfl

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem core_bound (region : V ⊆ S) : ∃ C : ℝ, ∀ v,
    ‖core hb hb1 c hc θ smoothθ compactθ supportθ v‖ ≤
      C * ‖ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 v‖ := by
  refine ⟨‖ManifoldHolderCutoffLocalization.localization e D atlas openV hb hb1
    c hc θ smoothθ compactθ supportθ‖, ?_⟩
  intro v
  change ‖(core hb hb1 c hc θ smoothθ compactθ supportθ v).val‖ ≤ _
  rw [core_graph e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ region]
  exact (ManifoldHolderCutoffLocalization.localization e D atlas openV hb hb1
    c hc θ smoothθ compactθ supportθ).le_opNorm _

@[expose] def localization : Global e D openV hb hb1 →L[ℂ]
    Local hb hb1 c θ compactθ supportθ :=
  (core hb hb1 c hc θ smoothθ compactθ supportθ).extendOfNorm
    (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1)

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem localization_smooth (region : V ⊆ S) (v : SmoothSupportedManifoldCore.core (E := E) V) :
    localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 v) =
        core hb hb1 c hc θ smoothθ compactθ supportθ v :=
  LinearMap.extendOfNorm_eq (ManifoldSmoothHolderCore.smooth_dense e D atlas openV hb hb1 region)
    (core_bound e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ region) v

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem physical_localization (region : V ⊆ S) (v : Global e D openV hb hb1) (y : E) :
    EuclideanSmoothHolderCore.physical
      (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
      (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ v) y =
        ChartLocalization.coordinate c θ (ManifoldSmoothHolderCore.physical e D openV hb hb1 v) y := by
  have left : Continuous (fun z : Global e D openV hb hb1 =>
      EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
        (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z) y) :=
    ((BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
      (EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1).continuous).comp
      (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ).continuous
  have right : Continuous (fun z : Global e D openV hb hb1 =>
      ChartLocalization.coordinate c θ (ManifoldSmoothHolderCore.physical e D openV hb hb1 z) y) := by
    by_cases inside : y ∈ c.target
    · simp only [ChartLocalization.coordinate, ite_eq_left inside]
      exact continuous_const.mul ((BoundedContinuousFunction.evalCLM ℂ (c.symm y)).continuous.comp
        (ManifoldSmoothHolderCore.physical e D openV hb hb1).continuous)
    · simp only [ChartLocalization.coordinate, ite_eq_right inside]
      exact continuous_const
  refine (ManifoldSmoothHolderCore.smooth_dense e D atlas openV hb hb1 region).induction_on
    (p := fun z => EuclideanSmoothHolderCore.physical
      (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
      (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z) y =
        ChartLocalization.coordinate c θ (ManifoldSmoothHolderCore.physical e D openV hb hb1 z) y)
    v (isClosed_eq left right) ?_
  intro w
  rw [localization_smooth e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ region]
  change BoundedHolderSpace.physical E b
    (core hb hb1 c hc θ smoothθ compactθ supportθ w).val y = _
  rw [core_graph e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ region,
    ManifoldHolderCutoffLocalization.physical_localization]

end LeanShared.ManifoldClosedCutoffHolderLocalization
