module
public import LeanShared.Geometry.FractionalManifoldCompositionOne
public import LeanShared.Geometry.FractionalOneJetLowering
public import Mathlib.Logic.Function.Iterate

/-! Actual positive iterates of a finite-regular manifold map retain the
lower C^(1+a) class needed by the canonical microlocal construction. -/
public noncomputable section
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Regular.iterate_one_add_of_pos {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→M}
    (regular:Regular (E:=E) (F:=E) (a+1) f) (n:ℕ) (positive:0<n) :
    Regular (E:=E) (F:=E) (a+1) (f^[n]) :=by
  have all:∀k:ℕ,Regular (E:=E) (F:=E) (a+1) (f^[k+1]):=by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add,Function.iterate_one] using regular
    | succ k ih =>
      have composed:=regular.comp_one_add_manifold ha ha1 ih
      simpa only [Function.iterate_succ'] using composed
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact all k

theorem Regular.iterate_lower_one_add {a r:ℝ} (ha:0<a) (ha1:a<1) (lower:a+1<r)
    {f:M→M} (regular:Regular (E:=E) (F:=E) r f) (n:ℕ) (positive:0<n) :
    Regular (E:=E) (F:=E) (a+1) (f^[n]) :=
  (FractionalOneJetLowering.regular_one_add ha ha1 lower regular).iterate_one_add_of_pos ha ha1 n positive
end LeanShared.FractionalManifoldRegularity
