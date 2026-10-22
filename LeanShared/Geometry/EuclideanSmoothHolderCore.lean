module
public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import LeanShared.Geometry.SmoothFractionalRegularity
public import LeanShared.Geometry.EuclideanFractionalHolder
public import LeanShared.Geometry.HolderFractionalRegularity
public import LeanShared.Geometry.BoundedHolderCore
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! The actual Euclidean supported little Hölder space. Smooth core
Hölder bounds are proved from their derivatives and support, rather than
supplied as a source. Every completed vector has the stated fractional
regularity and a faithful continuous function representation. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {V : Set E} (hV : IsCompact (closure V))
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

include hV in
omit [FiniteDimensional ℝ E] in
theorem compact_support (c : SmoothSupportedManifoldCore.core (E := E) V) :
    HasCompactSupport c.val :=
  hV.of_isClosed_subset (isClosed_tsupport _) (c.property.2.trans subset_closure)

@[expose] def smoothPhysical :
    SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] (E →ᵇ ℂ) where
  toFun c := ofCompactSupport c.val
    c.property.1.continuous (compact_support hV c)
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

include hb hb1 in
theorem smooth_holder (c : SmoothSupportedManifoldCore.core (E := E) V) :
    ∃ C : ℝ, ∀ x y, ‖smoothPhysical hV c x - smoothPhysical hV c y‖ ≤
      C * dist x y ^ b := by
  obtain ⟨C, _, bound⟩ := FractionalManifoldRegularity.global_holder_of_regular
    (smoothPhysical hV c) (compact_support hV c) hb hb1
    (FractionalManifoldRegularity.regular_of_smooth c.property.1 hb.le)
  exact ⟨C, by simpa only [dist_eq_norm] using bound⟩

@[expose] def core : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    BoundedHolderSpace.graph E b :=
  BoundedHolderSpace.liftCore E b (smoothPhysical hV) (smooth_holder hV hb hb1)

@[expose] def space : Submodule ℂ (BoundedHolderSpace.graph E b) :=
  DyadicCompletion.closedCore (core hV hb hb1)

instance complete : CompleteSpace (space hV hb hb1) := by
  unfold space
  infer_instance

@[expose] def smooth : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    space hV hb hb1 := DyadicCompletion.coreLift (core hV hb hb1)

theorem smooth_dense : DenseRange (smooth hV hb hb1) :=
  DyadicCompletion.coreLift_dense _

@[expose] def physical : space hV hb hb1 →L[ℂ] (E →ᵇ ℂ) :=
  (BoundedHolderSpace.physical E b).comp (space hV hb hb1).subtypeL

theorem physical_smooth (c : SmoothSupportedManifoldCore.core (E := E) V) :
    physical hV hb hb1 (smooth hV hb hb1 c) = smoothPhysical hV c := rfl

theorem physical_injective : Function.Injective (physical hV hb hb1) :=
  (BoundedHolderSpace.physical_injective E b).comp Subtype.val_injective

theorem regular (v : space hV hb hb1) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) b
      (fun x => physical hV hb hb1 v x) :=
  FractionalManifoldRegularity.graph_regular hb hb1 v.val

theorem physical_norm_le (v : space hV hb hb1) : ‖physical hV hb hb1 v‖ ≤ ‖v‖ :=
  BoundedHolderSpace.physical_norm_le E b v.val
end LeanShared.EuclideanSmoothHolderCore
