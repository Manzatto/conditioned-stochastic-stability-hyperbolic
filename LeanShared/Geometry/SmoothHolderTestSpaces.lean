module

public import LeanShared.Geometry.BoundedHolderCore
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Basic
public import LeanShared.Geometry.SmoothSupportedManifoldCore

/-! Concrete full and supported little Hölder test spaces on a compact
manifold. The only metric input is the ordinary Hölder estimate for actual
smooth functions; compatibility with finite charts must be supplied, not
inferred from an arbitrary compatible metric. -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.SmoothHolderTestSpaces
open SmoothSupportedManifoldCore DyadicCompletion
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M]

def smoothPhysical (V : Set M) : core (E := E) V →ₗ[ℂ] (M →ᵇ ℂ) where
  toFun c := BoundedContinuousFunction.mkOfCompact ⟨functions V c, (smooth V c).continuous⟩
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

def fullCoreInclusion (V : Set M) : core (E := E) V →ₗ[ℂ] core (E := E) (univ : Set M) where
  toFun c := ⟨c.val, c.property.1, subset_univ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

def holderCore (V : Set M) : core (E := E) V →ₗ[ℂ] BoundedHolderSpace.graph M u :=
  BoundedHolderSpace.liftCore M u (smoothPhysical V)
    (fun c => holder (fullCoreInclusion V c))

def space (V : Set M) : Submodule ℂ (BoundedHolderSpace.graph M u) :=
  closedCore (holderCore u holder V)


instance space_complete (V : Set M) : CompleteSpace (space u holder V) := by
  unfold space
  infer_instance

def coreMap (V : Set M) : core (E := E) V →ₗ[ℂ] space u holder V :=
  coreLift (holderCore u holder V)

theorem coreMap_dense (V : Set M) : DenseRange (coreMap u holder V) :=
  coreLift_dense (holderCore u holder V)

def physical (V : Set M) : space u holder V →L[ℂ] (M →ᵇ ℂ) :=
  (BoundedHolderSpace.physical M u).comp (space u holder V).subtypeL


@[simp] theorem physical_coreMap (V : Set M) (c : core (E := E) V) :
    physical u holder V (coreMap u holder V c) = smoothPhysical V c := rfl

def view (V : Set M) : space u holder V →ₗ[ℂ] (M → ℂ) where
  toFun v := physical u holder V v
  map_add' a b := by
    funext x
    exact congrArg (fun f : M →ᵇ ℂ => f x) ((physical u holder V).map_add a b)
  map_smul' a v := by
    funext x
    exact congrArg (fun f : M →ᵇ ℂ => f x) ((physical u holder V).map_smul a v)

def evaluate (V : Set M) (x : M) : space u holder V →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (physical u holder V)

theorem physical_norm_le (V : Set M) (v : space u holder V) :
    ‖physical u holder V v‖ ≤ ‖v‖ := BoundedHolderSpace.physical_norm_le M u v.val

theorem space_subset_full (V : Set M) : space u holder V ≤ space u holder univ := by
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨c, rfl⟩
  refine ⟨fullCoreInclusion V c, ?_⟩
  apply BoundedHolderSpace.physical_injective M u
  rfl

def includeFull (V : Set M) : space u holder V →L[ℂ] space u holder univ :=
  (space u holder V).subtypeL.codRestrict (space u holder univ)
    (fun v => space_subset_full u holder V v.property)

theorem include_physical (V : Set M) (v : space u holder V) :
    physical u holder univ (includeFull u holder V v) = physical u holder V v := rfl


instance holderGraphSeminormed : SeminormedAddCommGroup (BoundedHolderSpace.graph M u) :=
  (inferInstance : NormedAddCommGroup (BoundedHolderSpace.graph M u)).toSeminormedAddCommGroup

theorem includeFull_norm_le (V : Set M) : ‖includeFull u holder V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  exact le_rfl

theorem physical_injective (V : Set M) : Function.Injective (physical u holder V) :=
  (BoundedHolderSpace.physical_injective M u).comp Subtype.val_injective


theorem view_injective (V : Set M) : Function.Injective (view u holder V) := by
  intro a b h
  apply physical_injective u holder V
  apply BoundedContinuousFunction.ext
  exact congrFun h

theorem supported (V : Set M) (v : space u holder V) (x : M) (hx : x ∉ V) :
    physical u holder V v x = 0 := by
  exact BoundedHolderSpace.corePhysical_zero_outside M u (smoothPhysical V)
    (fun c => holder (fullCoreInclusion V c)) V (fun c y hy => zero_outside V c y hy) v x hx

def physicalOn (V K : Set M) : space u holder V →L[ℂ] (K →ᵇ ℂ) :=
  (BoundedContinuousFunction.compContinuousCLM ℂ ℂ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(K, M))).comp (physical u holder V)

theorem physicalOn_injective (V K : Set M) (hVK : V ⊆ K) :
    Function.Injective (physicalOn u holder V K) := by
  intro f g hfg
  apply physical_injective u holder V
  apply BoundedContinuousFunction.ext
  intro x
  by_cases hx : x ∈ K
  · exact congrArg (fun v : K →ᵇ ℂ => v ⟨x, hx⟩) hfg
  · have hnot : x ∉ V := fun h => hx (hVK h)
    rw [supported u holder V f x hnot, supported u holder V g x hnot]

end LeanShared.SmoothHolderTestSpaces
