module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! A genuine Banach derivative graph. Completeness is proved by uniform
limits of functions and derivatives; derivative compatibility is an actual
HasFDerivAt relation, not an independent regularity source. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace LeanShared.BoundedDerivativeGraph
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (q : H →L[ℂ] (E →ᵇ (E →L[ℝ] F)))

abbrev Ambient := (E →ᵇ F) × H

@[expose] def graph : Submodule ℂ (Ambient (E:=E) (F:=F) (H:=H)) where
  carrier := {v | ∀x,HasFDerivAt v.1 (q v.2 x) x}
  zero_mem' := by
    intro x
    change HasFDerivAt (fun _ : E => (0:F)) (q 0 x) x
    rw [map_zero]
    exact hasFDerivAt_const (0:F) x
  add_mem' {v w} hv hw := by
    intro x
    change HasFDerivAt (fun y => v.1 y+w.1 y) (q (v.2+w.2) x) x
    rw [map_add]
    exact (hv x).add (hw x)
  smul_mem' c v hv := by
    intro x
    change HasFDerivAt (fun y => c • v.1 y) (q (c • v.2) x) x
    rw [map_smul]
    exact (hv x).const_smul c

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem graph_closed : IsClosed (graph q : Set (Ambient (E:=E) (F:=F) (H:=H))) := by
  apply isSeqClosed_iff_isClosed.mp
  intro seq limit members tendsto
  have first : Tendsto (fun n => (seq n).1) atTop (𝓝 limit.1) := continuous_fst.continuousAt.tendsto.comp tendsto
  have second : Tendsto (fun n => q (seq n).2) atTop (𝓝 (q limit.2)) :=
    q.continuous.continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp tendsto)
  have uniform := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp second
  intro x
  exact hasFDerivAt_of_tendstoUniformly uniform (fun n y => members n y)
    (fun y => (BoundedContinuousFunction.evalCLM ℂ y).continuous.continuousAt.tendsto.comp first) x

instance complete [CompleteSpace H] : CompleteSpace (graph q) := (graph_closed q).completeSpace_coe

@[expose] def physical : graph q →L[ℂ] (E →ᵇ F) :=
  (ContinuousLinearMap.fst ℂ (E →ᵇ F) H).comp (graph q).subtypeL

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem physical_injective (faithful : Function.Injective q) : Function.Injective (physical q) := by
  intro v w equal
  apply Subtype.ext
  apply Prod.ext
  · exact equal
  · apply faithful
    apply BoundedContinuousFunction.ext
    intro x
    have hv := v.property x
    have first : v.val.1=w.val.1 := equal
    rw [first] at hv
    exact hv.unique (w.property x)

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem derivative (v : graph q) (x : E) : HasFDerivAt (physical q v) (q v.val.2 x) x := v.property x

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem contDiff_one (v : graph q) : ContDiff ℝ 1 (physical q v) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨q v.val.2, (q v.val.2).continuous, fun x => derivative q v x⟩
end LeanShared.BoundedDerivativeGraph
