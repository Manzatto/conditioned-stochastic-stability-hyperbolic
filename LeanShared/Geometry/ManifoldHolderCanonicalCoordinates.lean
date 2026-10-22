module
public import LeanShared.Geometry.ManifoldHolderLocalizationOperators

/-! Actual chart localization is a bounded right inverse to reconstruction
on the constructed global little Holder quotient. Consequently its literal
coordinate graph norm controls the global quotient norm. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldHolderCanonicalCoordinates
open ManifoldHolderCoordinateOperators
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  (e : J→OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0<b) (hb1 : b<1)

abbrev Regular := ManifoldSmoothHolderCore.Lower e D openV hb hb1
abbrev Coordinates := ManifoldHolderQuotient.Coordinates (regions e D openV) hb hb1
local instance coordinateNormed : NormedAddCommGroup (Coordinates e D openV hb hb1) := inferInstance
local instance coordinateSemi : SeminormedAddCommGroup (Coordinates e D openV hb hb1) :=
  (coordinateNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance coordinateScalar : NormedSpace ℂ (Coordinates e D openV hb hb1) := inferInstance
local instance regularNormed : NormedAddCommGroup (Regular e D openV hb hb1) := inferInstance
local instance regularSemi : SeminormedAddCommGroup (Regular e D openV hb hb1) :=
  (regularNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance regularScalar : NormedSpace ℂ (Regular e D openV hb hb1) := inferInstance

@[expose] def coordinates : Regular e D openV hb hb1→L[ℂ]Coordinates e D openV hb hb1 :=
  ContinuousLinearMap.pi (ManifoldHolderLocalizationOperators.localization e D atlas openV hb hb1)

theorem localization_physical (v : Regular e D openV hb hb1) (i : D.indices) (y : E) :
    EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
      (coordinates e D atlas openV hb hb1 v i) y =
    ChartLocalization.coordinate (e i) (D.cutoff i)
      (ManifoldSmoothHolderCore.physical e D openV hb hb1 v) y := by
  obtain ⟨z,rfl⟩ := BanachFunctionQuotient.quotient_surjective
    (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1) v
  change EuclideanSmoothHolderCore.physical _ hb hb1
    (ManifoldHolderLocalizationOperators.localization e D atlas openV hb hb1 i
      (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1 z)) y = _
  rw [ManifoldHolderLocalizationOperators.localization_quotient]
  have physical := ManifoldHolderQuotient.physical_quotient (regions e D openV) hb hb1 z
  exact (ManifoldHolderLocalizationOperators.row_physical e D atlas openV hb hb1 i z y).trans
    (congrArg (fun f:M→ᵇℂ=>ChartLocalization.coordinate (e i) (D.cutoff i) f y) physical.symm)

theorem quotient_coordinates (region : V⊆S) (v : Regular e D openV hb hb1) :
    ManifoldHolderQuotient.quotient (regions e D openV) hb hb1
      (coordinates e D atlas openV hb hb1 v)=v := by
  refine (ManifoldSmoothHolderCore.smooth_dense e D atlas openV hb hb1 region).induction_on v
    (isClosed_eq ((ManifoldHolderQuotient.quotient (regions e D openV) hb hb1).continuous.comp
      (coordinates e D atlas openV hb hb1).continuous) continuous_id) ?_
  intro c
  have localIdentity : coordinates e D atlas openV hb hb1
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)=
      ManifoldSmoothHolderCore.smoothCoordinates e D atlas openV hb hb1 c := by
    funext i
    exact ManifoldHolderLocalizationOperators.localization_smooth e D atlas openV hb hb1 region i c
  exact congrArg (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1) localIdentity

theorem norm_le_coordinates (region : V⊆S) (v : Regular e D openV hb hb1) :
    ‖v‖ ≤ ‖coordinates e D atlas openV hb hb1 v‖ := by
  conv_lhs => rw [←quotient_coordinates e D atlas openV hb hb1 region v]
  exact Submodule.Quotient.norm_mk_le _ _
end LeanShared.ManifoldHolderCanonicalCoordinates
