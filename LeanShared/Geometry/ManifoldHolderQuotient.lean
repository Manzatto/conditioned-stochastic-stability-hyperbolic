module
public import LeanShared.Geometry.EuclideanLittleChartExtension
public import LeanShared.Geometry.BanachFunctionQuotient
public import LeanShared.Geometry.ChartSmoothingRegions
public import LeanShared.Geometry.FiniteHolderChartPatching
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.Normed.Group.Quotient

/-! A constructed lower-regularity Banach space on the actual manifold.
Take the finite product of concrete little Hölder chart spaces, reconstruct
literal functions, and quotient by the closed reconstruction kernel.
Faithfulness, completeness and actual fractional regularity are proved.
This avoids a supplied global regular space or an arbitrary metric claim. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldHolderQuotient
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
  (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

abbrev Coordinates := ∀ i, EuclideanSmoothHolderCore.space (d.compact_closure i) hb hb1

local instance coordinatesNormed : NormedAddCommGroup (Coordinates d hb hb1) := inferInstance
local instance coordinatesSeminormed : SeminormedAddCommGroup (Coordinates d hb hb1) :=
  (coordinatesNormed d hb hb1).toSeminormedAddCommGroup
local instance coordinatesScalar : NormedSpace ℂ (Coordinates d hb hb1) := inferInstance

@[expose] def supportedCoordinates : Coordinates d hb hb1 →L[ℂ]
    (∀ i, SupportedHolderChartSpace.space (a := b) (closure (d.region i))) :=
  ContinuousLinearMap.pi fun i =>
    (EuclideanLittleChartExtension.supported (d.compact_closure i) hb hb1).comp
      (ContinuousLinearMap.proj i)

@[expose] def reconstruction : Coordinates d hb hb1 →L[ℂ] (M →ᵇ ℂ) :=
  (FiniteHolderChartPatching.reconstruction b (fun i => closure (d.region i))
    d.compact_closure e d.closure_target).comp (supportedCoordinates d hb hb1)

abbrev Space := BanachFunctionQuotient.Space (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1)

@[expose] def quotient : Coordinates d hb hb1 →L[ℂ] Space d hb hb1 :=
  BanachFunctionQuotient.quotient (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1)

@[expose] def physical : Space d hb hb1 →L[ℂ] (M →ᵇ ℂ) :=
  BanachFunctionQuotient.physical (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1)

omit [ChartedSpace E M] in
theorem physical_quotient (z : Coordinates d hb hb1) :
    physical d hb hb1 (quotient d hb hb1 z) = reconstruction d hb hb1 z :=
  BanachFunctionQuotient.physical_quotient (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) _ z

omit [ChartedSpace E M] in
theorem physical_injective : Function.Injective (physical d hb hb1) :=
  BanachFunctionQuotient.physical_injective (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) _

theorem reconstruction_regular [IsManifold (𝓘(ℝ,E)) ∞ M]
    (atlas : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (z : Coordinates d hb hb1) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) b
      (fun x => reconstruction d hb hb1 z x) :=
  FiniteHolderChartPatching.reconstruction_regular b (fun i => closure (d.region i))
    d.compact_closure e d.closure_target atlas hb hb1
      (supportedCoordinates d hb hb1 z)

theorem regular [IsManifold (𝓘(ℝ,E)) ∞ M]
    (atlas : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (v : Space d hb hb1) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) b
      (fun x => physical d hb hb1 v x) := by
  obtain ⟨z, rfl⟩ := BanachFunctionQuotient.quotient_surjective (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1) v
  exact reconstruction_regular d hb hb1 atlas z
end LeanShared.ManifoldHolderQuotient
