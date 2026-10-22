module
public import LeanShared.Dynamics.HyperbolicAdaptedWholeFrame
public import LeanShared.Geometry.FiniteBundleSectionCombination

/-! Joint continuity of the actual adapted coordinate maps in their local
base point and their Euclidean argument, in the original tangent bundle. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedFramePatches.LocalFrame
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
  {S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)}
  {d : ℕ} {a : ℝ} {N : ℕ} {x : Λ}

theorem continuous_coordinate_section (F : LocalFrame h S d a N x) (c : Fin d → ℝ) :
    Continuous (fun y : ↥(Λ ∩ F.neighborhood) =>
      (⟨y.val, (F.coordinates y c).val⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  exact FiniteBundleSectionCombination.continuous_combination
    (fun y : M => TangentSpace (𝓘(ℝ, E)) y) Subtype.val continuous_subtype_val
    F.vector F.continuous (fun _ => c) (fun _ => continuous_const)

theorem continuous_euclidean_section (F : LocalFrame h S d a N x)
    (c : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun y : ↥(Λ ∩ F.neighborhood) =>
      (⟨y.val, (F.euclideanCoordinates y c).val⟩ : TangentBundle (𝓘(ℝ, E)) M)) :=
  F.continuous_coordinate_section (fun i => c i)

theorem joint_euclidean (F : LocalFrame h S d a N x) :
    Continuous (fun p : ↥(Λ ∩ F.neighborhood) × EuclideanSpace ℝ (Fin d) =>
      (⟨p.1.val, (F.euclideanCoordinates p.1 p.2).val⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  exact ContinuousSubspaceFrameNormalization.joint_linear
    (fun y : M => TangentSpace (𝓘(ℝ, E)) y) Subtype.val continuous_subtype_val
    (fun y => (S y.val).subtypeL.comp (F.euclideanCoordinates y).toContinuousLinearMap)
    F.continuous_euclidean_section

end LeanShared.HyperbolicAdaptedFramePatches.LocalFrame
