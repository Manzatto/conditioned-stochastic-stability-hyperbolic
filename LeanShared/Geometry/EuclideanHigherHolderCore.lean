module
public import LeanShared.Geometry.HigherDerivativeHolderCore
public import LeanShared.Geometry.HigherDerivativeHolderRegular
public import LeanShared.Geometry.SmoothSupportedManifoldCore

/-! Concrete exact-support smooth-core Banach spaces at every order n+a
on finite-dimensional Euclidean model spaces. The complete graph and its
actual smooth closure are constructed, with faithful function views. -/
public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.EuclideanHigherHolderCore
open HigherDerivativeHolderSpace
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V:Set E} (compactV:IsCompact (closure V)) {a:ℝ} (ha:0<a) (ha1:a<1) (n:ℕ)

@[expose] def model := constructFull (E:=E) (F:=ℂ) ha ha1 n

omit [FiniteDimensional ℝ E] in
theorem core_smooth (c:SmoothSupportedManifoldCore.core (E:=E) V) : ContDiff ℝ ∞ c.val :=
  c.property.1.contDiff

include compactV in
omit [FiniteDimensional ℝ E] in
theorem core_compact (c:SmoothSupportedManifoldCore.core (E:=E) V) : HasCompactSupport c.val :=
  compactV.of_isClosed_subset (isClosed_tsupport _) (c.property.2.trans subset_closure)

@[expose] def space := little (model ha ha1 n).toModel
  (SmoothSupportedManifoldCore.core (E:=E) V) core_smooth (core_compact compactV)

instance complete : CompleteSpace (space compactV ha ha1 n) := by unfold space;infer_instance

@[expose] def smooth : SmoothSupportedManifoldCore.core (E:=E) V→ₗ[ℂ]space compactV ha ha1 n :=
  smoothLift (model ha ha1 n).toModel
    (SmoothSupportedManifoldCore.core (E:=E) V) core_smooth (core_compact compactV)

@[expose] def physical : space compactV ha ha1 n→L[ℂ](E→ᵇℂ) :=
  littlePhysical (model ha ha1 n).toModel
    (SmoothSupportedManifoldCore.core (E:=E) V) core_smooth (core_compact compactV)

theorem smooth_dense : DenseRange (smooth compactV ha ha1 n) :=
  HigherDerivativeHolderSpace.smooth_dense _ _ _ _

theorem physical_smooth (c:SmoothSupportedManifoldCore.core (E:=E) V) (x:E) :
    physical compactV ha ha1 n (smooth compactV ha ha1 n c) x=c.val x :=
  littlePhysical_smooth _ _ _ _ c x

theorem physical_injective : Function.Injective (physical compactV ha ha1 n) :=
  littlePhysical_injective _ _ _ _

theorem physical_norm_le (v:space compactV ha ha1 n) :
    ‖physical compactV ha ha1 n v‖≤‖v‖ := littlePhysical_norm_le _ _ _ _ v

theorem regular (v:space compactV ha ha1 n) :
    FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) (a+n)
      (physical compactV ha ha1 n v) := little_regular _ _ _ _ v
end LeanShared.EuclideanHigherHolderCore
