module
public import LeanShared.Geometry.HigherFractionalBilinear
public import LeanShared.Geometry.FractionalRegularLinearMap
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! Scalar multiplication preserves every real regularity order. Scalar
universe lifting lets the proved all-order bilinear jet theorem apply to
manifold models in arbitrary universes. -/
public noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
universe u
variable {E:Type u} {M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem Regular.mul {r:ℝ} {f g:M→ℝ}
    (hf:Regular (E:=E) (F:=ℝ) r f) (hg:Regular (E:=E) (F:=ℝ) r g) :
    Regular (E:=E) (F:=ℝ) r (fun x=>f x*g x) := by
  by_cases integer:r=(⌊r⌋₊:ℝ)
  · exact ⟨hf.nonnegative,hf.differentiable.mul hg.differentiable,fun unequal=>False.elim (unequal integer)⟩
  let a := r-(⌊r⌋₊:ℝ)
  have ha:0<a := lt_of_le_of_ne (sub_nonneg.mpr (Nat.floor_le hf.nonnegative)) (by
    intro zero
    apply integer
    dsimp [a] at zero
    linarith)
  have ha1:a<1 := Nat.self_sub_floor_lt_one r
  have order:a+(⌊r⌋₊:ℝ)=r := sub_add_cancel _ _
  let down:ULift.{u} ℝ →L[ℝ] ℝ := ContinuousLinearEquiv.ulift.toContinuousLinearMap
  let up:ℝ →L[ℝ] ULift.{u} ℝ := ContinuousLinearEquiv.ulift.symm.toContinuousLinearMap
  have left : Regular (E:=E) (F:=ULift.{u} ℝ) (a+(⌊r⌋₊:ℝ)) (fun x=>up (f x)) := by
    rw [order]
    exact hf.comp_continuousLinearMap up
  have right : Regular (E:=E) (F:=ULift.{u} ℝ) (a+(⌊r⌋₊:ℝ)) (fun x=>up (g x)) := by
    rw [order]
    exact hg.comp_continuousLinearMap up
  have product := left.bilinear_noninteger ha ha1 right (ContinuousLinearMap.mul ℝ (ULift.{u} ℝ))
  have result := product.comp_continuousLinearMap down
  rw [order] at result
  exact result

end LeanShared.FractionalManifoldRegularity
