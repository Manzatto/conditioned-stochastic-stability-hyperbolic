module
public import LeanShared.Analysis.CommonAmbientOuterResolvent
public import LeanShared.Analysis.AnalyticResolvent
public import LeanShared.Analysis.MeromorphicIdentity
public import LeanShared.Analysis.MeromorphicLinearMap
public import LeanShared.Analysis.ExteriorConnected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Linarith

/-! Actual meromorphic resolvents agreeing in the outer Neumann region
agree at every common resolvent point outside the contraction disk. No
completeness of the common ambient distribution space is added. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.MeromorphicCommonResolvent
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem eq (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (actionA : a.comp P = L.comp a) (actionB : b.comp Q = L.comp b)
    (x : E) (y : F) (common : a x = b y)
    (r : ℝ) (hr : 0 ≤ r)
    (meromorphicP : MeromorphicOn (fun z : ℂ => resolvent P z) {z | r < ‖z‖})
    (meromorphicQ : MeromorphicOn (fun z : ℂ => resolvent Q z) {z | r < ‖z‖})
    (z : ℂ) (hz : r < ‖z‖) (resP : z ∈ resolventSet ℂ P) (resQ : z ∈ resolventSet ℂ Q) :
    a ((resolvent P z) x) = b ((resolvent Q z) y) := by
  let S : Set ℂ := {w | r < ‖w‖}
  let R := ‖P‖ + ‖Q‖ + r + 1
  let w : ℂ := R
  have positive : 0 ≤ R := by dsimp only [R]; linarith [norm_nonneg P, norm_nonneg Q]
  have normW : ‖w‖ = R := by simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg positive]
  have member : w ∈ S := by
    change r < ‖w‖
    rw [normW]
    dsimp only [R]
    linarith [norm_nonneg P, norm_nonneg Q]
  have largeP : ‖P‖ < ‖w‖ := by rw [normW]; dsimp only [R]; linarith [norm_nonneg Q]
  have largeQ : ‖Q‖ < ‖w‖ := by rw [normW]; dsimp only [R]; linarith [norm_nonneg P]
  have mf : MeromorphicOn (fun v => a ((resolvent P v) x)) S := fun v hv =>
    MeromorphicLinearMap.map (a.comp (ContinuousLinearMap.apply ℂ E x)) (meromorphicP v hv)
  have mg : MeromorphicOn (fun v => b ((resolvent Q v) y)) S := fun v hv =>
    MeromorphicLinearMap.map (b.comp (ContinuousLinearMap.apply ℂ F y)) (meromorphicQ v hv)
  have near : (fun v => a ((resolvent P v) x)) =ᶠ[𝓝 w] (fun v => b ((resolvent Q v) y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds largeP,
      (isOpen_lt continuous_const continuous_norm).mem_nhds largeQ] with v hvP hvQ
    exact CommonAmbientOuterResolvent.eq P Q L a b actionA actionB x y common v hvP hvQ
  apply MeromorphicIdentity.eq_of_eventuallyEq mf mg
    (ExteriorConnected.isPreconnected (E := ℂ) (by simp [Complex.rank_real_complex]) hr) member near hz
  · exact (((a.comp (ContinuousLinearMap.apply ℂ E x)).analyticAt _).comp
      (AnalyticResolvent.analyticAt P resP)).continuousAt
  · exact (((b.comp (ContinuousLinearMap.apply ℂ F y)).analyticAt _).comp
      (AnalyticResolvent.analyticAt Q resQ)).continuousAt
end LeanShared.MeromorphicCommonResolvent
