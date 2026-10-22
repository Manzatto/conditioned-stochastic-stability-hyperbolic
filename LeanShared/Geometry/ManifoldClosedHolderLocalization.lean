module
public import LeanShared.Geometry.ManifoldHolderLocalizationOperators
public import LeanShared.Geometry.CompactSchwartzHolderCore

/-! Actual global-to-local maps into the little Hölder closure on each
literal compact chart support, constructed before any transfer model. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldClosedHolderLocalization
variable {E M J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0<b) (hb1 : b<1)

abbrev Local (i : D.indices) := EuclideanSmoothHolderCore.space
  (ConstructedManifoldLocalization.support_compact e D i).closure hb hb1
abbrev Global := ManifoldSmoothHolderCore.Lower e D openV hb hb1
local instance globalNormed : NormedAddCommGroup (Global e D openV hb hb1) := inferInstance
local instance globalSemi : SeminormedAddCommGroup (Global e D openV hb hb1) :=
  (globalNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance globalScalar : NormedSpace ℂ (Global e D openV hb hb1) := inferInstance
local instance localNormed (i:D.indices) : NormedAddCommGroup (Local e D hb hb1 i) := inferInstance
local instance localSemi (i:D.indices) : SeminormedAddCommGroup (Local e D hb hb1 i) :=
  (localNormed e D hb hb1 i).toSeminormedAddCommGroup
local instance localScalar (i:D.indices) : NormedSpace ℂ (Local e D hb hb1 i) := inferInstance

local instance openLocalNormed (i:D.indices) : NormedAddCommGroup
    (ManifoldHolderCoordinateOperators.Local e D openV hb hb1 i) := inferInstance
local instance openLocalSemi (i:D.indices) : SeminormedAddCommGroup
    (ManifoldHolderCoordinateOperators.Local e D openV hb hb1 i) :=
  (openLocalNormed e D openV hb hb1 i).toSeminormedAddCommGroup
local instance openLocalScalar (i:D.indices) : NormedSpace ℂ
    (ManifoldHolderCoordinateOperators.Local e D openV hb hb1 i) := inferInstance

@[expose] def core (i:D.indices) : SmoothSupportedManifoldCore.core (E:=E) V →ₗ[ℂ] Local e D hb hb1 i :=
  (CompactSchwartzHolderCore.core (ConstructedManifoldLocalization.support_compact e D i) hb hb1).comp
    (ConstructedManifoldLocalization.localize e D atlas
      (SmoothSupportedManifoldCore.functions V) (fun c=>c.property.1) i)

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem core_norm (i:D.indices) (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    ‖core e D atlas hb hb1 i c‖ =
    ‖EuclideanSmoothHolderCore.smooth
      ((ManifoldSmoothHolderCore.regions e D openV).compact_closure i) hb hb1
      (ManifoldSmoothHolderCore.localCore e D atlas openV i c)‖ := by
  change ‖(core e D atlas hb hb1 i c).val‖ = ‖(EuclideanSmoothHolderCore.smooth _ hb hb1 _).val‖
  congr 1

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem bound (region:V⊆S) (i:D.indices) : ∃C:ℝ, ∀c,
    ‖core e D atlas hb hb1 i c‖ ≤ C*‖ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c‖ := by
  refine ⟨‖ManifoldHolderLocalizationOperators.localization e D atlas openV hb hb1 i‖,?_⟩
  intro c
  calc
    _ = ‖ManifoldHolderLocalizationOperators.localization e D atlas openV hb hb1 i
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)‖ := by
        exact (core_norm e D atlas openV hb hb1 i c).trans
          (congrArg norm (ManifoldHolderLocalizationOperators.localization_smooth
            e D atlas openV hb hb1 region i c)).symm
    _ ≤ _ := (ManifoldHolderLocalizationOperators.localization e D atlas openV hb hb1 i).le_opNorm _

@[expose] def localization (i:D.indices) : Global e D openV hb hb1 →L[ℂ] Local e D hb hb1 i :=
  (core e D atlas hb hb1 i).extendOfNorm (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1)

include atlas in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem localization_smooth (region:V⊆S) (i:D.indices) (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    localization e D atlas openV hb hb1 i (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)=
      core e D atlas hb hb1 i c :=
  LinearMap.extendOfNorm_eq (ManifoldSmoothHolderCore.smooth_dense e D atlas openV hb hb1 region)
    (bound e D atlas openV hb hb1 region i) c
end LeanShared.ManifoldClosedHolderLocalization
