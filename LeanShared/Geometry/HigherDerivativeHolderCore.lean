module
public import LeanShared.Geometry.HigherDerivativeHolderSpace
public import LeanShared.Analysis.DyadicCompletion

/-! Actual linear smooth-core realization and little-space closure in every
constructed finite derivative Holder graph. Smooth density is obtained in
the closed smooth range, while physical derivatives remain compatible. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.HigherDerivativeHolderSpace
universe u
variable {E F:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {r:ℝ} (d:Model E F r) (S:Submodule ℂ (E→F))
  (smooth:∀c:S,ContDiff ℝ ∞ c.val) (compact:∀c:S,HasCompactSupport c.val)

@[expose] def represent (c:S) : d.carrier :=
  Classical.choose (d.represents_smooth c.val (smooth c) (compact c))

theorem physical_represent (c:S) (x:E) :
    d.physical (represent d S smooth compact c) x=c.val x :=
  Classical.choose_spec (d.represents_smooth c.val (smooth c) (compact c)) x

@[expose] def core : S→ₗ[ℂ]d.carrier where
  toFun:=represent d S smooth compact
  map_add' c f:=by
    apply d.faithful
    ext x
    simp only [map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,physical_represent,
      Submodule.coe_add]
  map_smul' z c:=by
    apply d.faithful
    ext x
    simp only [map_smul,BoundedContinuousFunction.coe_smul,Pi.smul_apply,physical_represent,
      Submodule.coe_smul,RingHom.id_apply]

@[expose] def little : Submodule ℂ d.carrier :=
  DyadicCompletion.closedCore (core d S smooth compact)

instance little_complete : CompleteSpace (little d S smooth compact) := by
  unfold little DyadicCompletion.closedCore
  infer_instance

@[expose] def smoothLift : S→ₗ[ℂ]little d S smooth compact :=
  DyadicCompletion.coreLift (core d S smooth compact)

theorem smooth_dense : DenseRange (smoothLift d S smooth compact) :=
  DyadicCompletion.coreLift_dense _

@[expose] def littlePhysical : little d S smooth compact→L[ℂ](E→ᵇF) :=
  d.physical.comp (little d S smooth compact).subtypeL

theorem littlePhysical_injective : Function.Injective (littlePhysical d S smooth compact) :=
  d.faithful.comp Subtype.val_injective

theorem littlePhysical_smooth (c:S) (x:E) :
    littlePhysical d S smooth compact (smoothLift d S smooth compact c) x=c.val x :=
  physical_represent d S smooth compact c x

theorem little_regular (v:little d S smooth compact) :
    FractionalManifoldRegularity.Regular (E:=E) (F:=F) r
      (littlePhysical d S smooth compact v) := d.regular v.val

theorem littlePhysical_norm_le (v:little d S smooth compact) :
    ‖littlePhysical d S smooth compact v‖≤‖v‖ := d.physical_norm_le v.val
end LeanShared.HigherDerivativeHolderSpace
