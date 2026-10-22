module

public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The physical C0 realization of the actual little regular completion.
Its dense smooth core consists of literal supported manifold functions. An
ordinary Cu-to-uniform bound constructs the physical map; pointwise values
and zero extension follow by density, not by source compatibility fields. -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  (V K : Set M) [CompactSpace K]

def physicalCore : core (E := E) V →ₗ[ℂ] (K →ᵇ ℂ) where
  toFun f := BoundedContinuousFunction.mkOfCompact
    ⟨(fun x : K => functions V f x.val), (smooth V f).continuous.comp continuous_subtype_val⟩
  map_add' _f _g := BoundedContinuousFunction.ext fun _x => rfl
  map_smul' _c _f := BoundedContinuousFunction.ext fun _x => rfl

@[simp] theorem physicalCore_apply (f : core (E := E) V) (x : K) :
    physicalCore (E := E) V K f x = functions V f x.val := rfl

variable (q : core (E := E) V →ₗ[ℂ] Reg) (dense : DenseRange q)
  (C : ℝ) (hbound : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖q c‖)

def physicalRealization : Reg →L[ℂ] (K →ᵇ ℂ) := (physicalCore V K).extendOfNorm q

include dense hbound in
omit [CompleteSpace Reg] in
theorem physicalRealization_core (c : core (E := E) V) :
    physicalRealization V K q (q c) = physicalCore V K c :=
  LinearMap.extendOfNorm_eq (f := physicalCore V K) (e := q) dense ⟨C, hbound⟩ c

variable (evaluate : M → Reg →L[ℂ] ℂ)
  (hevaluate : ∀ x c, evaluate x (q c) = functions V c x)

include dense hbound hevaluate in
omit [CompleteSpace Reg] in
theorem physicalRealization_value (v : Reg) (x : K) :
    physicalRealization V K q v x = evaluate x.val v := by
  apply dense.induction_on
    (p := fun v => physicalRealization V K q v x = evaluate x.val v) v
    (isClosed_eq ((BoundedContinuousFunction.evalCLM (𝕜 := ℂ) x).continuous.comp
      (physicalRealization V K q).continuous) (evaluate x.val).continuous)
  intro c
  rw [physicalRealization_core V K q dense C hbound]
  exact (hevaluate x.val c).symm

include dense hevaluate in
omit [CompleteSpace Reg] [CompactSpace K] in
theorem evaluate_zero_outside_live (hVK : V ⊆ K) (v : Reg) (x : M) (hx : x ∉ K) :
    evaluate x v = 0 := by
  apply dense.induction_on (p := fun v => evaluate x v = 0) v
    (isClosed_eq (evaluate x).continuous continuous_const)
  intro c
  rw [hevaluate]
  exact zero_outside V c x (fun h => hx (hVK h))

end LeanShared.SmoothSupportedManifoldCore
