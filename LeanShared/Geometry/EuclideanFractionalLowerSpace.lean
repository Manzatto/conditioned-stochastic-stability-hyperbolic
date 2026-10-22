module
public import LeanShared.Geometry.EuclideanAnyOrderHolderRealization

/-! A concrete lower-space producer for every actual supported Euclidean
C^u core, u>b and 0<b<1. All representation, faithfulness, regularity,
density and exact-support approximation facts are derived. The remaining
anisotropic norm estimate is intentionally not part of this construction. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold BoundedContinuousFunction
namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {V : Set E} (hV : IsCompact (closure V)) (openV : IsOpen V)
  {b u : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbu : b < u)

@[expose] def RoughFunctions (u : ℝ) (V : Set E) :=
  {f : E → ℂ // FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u f ∧ tsupport f ⊆ V}

include hV in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem rough_compact_support (f : RoughFunctions u V) : HasCompactSupport f.val :=
  hV.of_isClosed_subset (isClosed_tsupport _) (f.property.2.trans subset_closure)

@[expose] def roughPhysical (f : RoughFunctions u V) : E →ᵇ ℂ :=
  ofCompactSupport f.val f.property.1.differentiable.continuous (rough_compact_support hV f)

include μ openV hbu in
theorem rough_exists (f : RoughFunctions u V) :
    ∃ v : space hV hb hb1, physical hV hb hb1 v = roughPhysical hV f :=
  exists_lower_of_any_regular μ hV hb hb1 (roughPhysical hV f) openV
    f.property.2 (rough_compact_support hV f) hbu f.property.1

@[expose] def lower (f : RoughFunctions u V) : space hV hb hb1 :=
  Classical.choose (rough_exists μ hV openV hb hb1 hbu f)

theorem physical_lower (f : RoughFunctions u V) :
    physical hV hb hb1 (lower μ hV openV hb hb1 hbu f) = roughPhysical hV f :=
  Classical.choose_spec (rough_exists μ hV openV hb hb1 hbu f)

@[expose] def view : space hV hb hb1 →ₗ[ℂ] (E → ℂ) where
  toFun v := physical hV hb hb1 v
  map_add' a b := by funext x; exact congrArg (fun f : E →ᵇ ℂ => f x) ((physical hV hb hb1).map_add a b)
  map_smul' a b := by funext x; exact congrArg (fun f : E →ᵇ ℂ => f x) ((physical hV hb hb1).map_smul a b)

omit [MeasurableSpace E] [BorelSpace E] in
theorem view_injective : Function.Injective (view hV hb hb1) := by
  intro f g equal
  apply physical_injective hV hb hb1
  ext x
  exact congrFun equal x

theorem view_lower (f : RoughFunctions u V) :
    view hV hb hb1 (lower μ hV openV hb hb1 hbu f) = f.val := by
  funext x
  exact congrArg (fun g : E →ᵇ ℂ => g x) (physical_lower μ hV openV hb hb1 hbu f)

omit [MeasurableSpace E] [BorelSpace E] in
theorem view_smooth (c : SmoothSupportedManifoldCore.core (E := E) V) :
    view hV hb hb1 (smooth hV hb hb1 c) = c.val := rfl

theorem approximate (f : RoughFunctions u V) :
    ∃ c : ℕ → SmoothSupportedManifoldCore.core (E := E) V,
      Tendsto (fun n => smooth hV hb hb1 (c n)) atTop
        (𝓝 (lower μ hV openV hb hb1 hbu f)) :=
  exists_smooth_sequence hV hb hb1 _
end LeanShared.EuclideanSmoothHolderCore
