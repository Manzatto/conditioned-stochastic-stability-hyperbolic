module
public import LeanShared.Dynamics.HyperbolicAdaptedWholeFrame
public import LeanShared.Dynamics.HyperbolicAdaptedOneStepBlocks
import Mathlib.Tactic.Linarith

/-! The first two adapted-atlas data assembled from actual BasicData:
one adapted time, one contraction rate, fixed dimensions, continuous local
frames, a finite compact smaller cover and uniform original-norm bounds. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedForms HyperbolicAdaptedFramePatches
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

structure PatchSystem (b : BasicData (E := E) T Λ V) where
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  slack : b.hyperbolic.contraction < rate
  time : ℕ
  time_pos : 0 < time
  framing : IsometricFraming b.hyperbolic
  stableFrame : ∀ x : Λ, LocalFrame b.hyperbolic b.hyperbolic.stable
    framing.stableDimension rate time x
  unstableFrame : ∀ x : Λ, LocalFrame b.hyperbolic b.hyperbolic.unstable
    framing.unstableDimension rate time x
  centers : Finset Λ
  patch : Λ → Set Λ
  patch_properties : ∀ x, IsCompact (patch x) ∧
    (∀ y ∈ patch x, y.val ∈ (stableFrame x).neighborhood ∧
      y.val ∈ (unstableFrame x).neighborhood) ∧ x ∈ interior (patch x)
  covering : (univ : Set Λ) ⊆ ⋃ x ∈ centers, interior (patch x)
  comparison : ℝ
  comparison_pos : 0 < comparison
  norm_comparison : ∀ x ∈ Λ, ∀ v : TangentSpace (𝓘(ℝ, E)) x,
    ‖v‖ ^ 2 ≤ 2 * splitForm T T.symm b.hyperbolic.projection rate time x v v ∧
      splitForm T T.symm b.hyperbolic.projection rate time x v v ≤ comparison * ‖v‖ ^ 2
  stable_step : ∀ x ∈ Λ, ∀ v ∈ b.hyperbolic.stable x,
    splitForm T T.symm b.hyperbolic.projection rate time (T x)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v) ≤
      rate ^ 2 * splitForm T T.symm b.hyperbolic.projection rate time x v v
  unstable_step : ∀ x ∈ Λ, ∀ v ∈ b.hyperbolic.unstable x,
    splitForm T T.symm b.hyperbolic.projection rate time (T.symm x)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v) ≤
      rate ^ 2 * splitForm T T.symm b.hyperbolic.projection rate time x v v
  inverse_bound : ℝ
  inverse_bound_pos : 0 < inverse_bound
  whole_bounds : ∀ (x : Λ)
    (y : ↥(Λ ∩ ((unstableFrame x).neighborhood ∩ (stableFrame x).neighborhood))),
    ‖(wholeFrame (unstableFrame x) (stableFrame x) y).toContinuousLinearMap‖ ≤ 2 ∧
      ‖(wholeFrame (unstableFrame x) (stableFrame x) y).symm.toContinuousLinearMap‖ ≤ inverse_bound

theorem exists_system (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M)) :
    Nonempty (PatchSystem b) := by
  let a := (b.hyperbolic.contraction + 1) / 2
  have positive : 0 < a := by dsimp only [a]; linarith [b.hyperbolic.contraction_pos]
  have below : a < 1 := by dsimp only [a]; linarith [b.hyperbolic.contraction_lt_one]
  have slack : b.hyperbolic.contraction < a := by
    dsimp only [a]; linarith [b.hyperbolic.contraction_lt_one]
  obtain ⟨N, length, stable, unstable⟩ :=
    HyperbolicAdaptedContraction.exists_one_step b.hyperbolic forward backward a slack
  obtain ⟨framing⟩ := b.exists_isometricFraming
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero)
  obtain ⟨Fs, Fu, centers, patch, properties, covers⟩ :=
    compact_cover b.hyperbolic framing forward backward a N length
  obtain ⟨B, positiveB, comparison⟩ :=
    HyperbolicAdaptedUniformComparison.uniform_comparison b.hyperbolic a N length
  obtain ⟨C, positiveC, frameBounds⟩ := wholeFrame_uniform_bounds b.hyperbolic a N length
  exact ⟨{
    rate := a
    rate_pos := positive
    rate_lt_one := below
    slack := slack
    time := N
    time_pos := length
    framing := framing
    stableFrame := Fs
    unstableFrame := Fu
    centers := centers
    patch := patch
    patch_properties := properties
    covering := covers
    comparison := B
    comparison_pos := positiveB
    norm_comparison := comparison
    stable_step := stable
    unstable_step := unstable
    inverse_bound := C
    inverse_bound_pos := positiveC
    whole_bounds := fun x y => frameBounds _ _ x (Fu x) (Fs x) y }⟩

@[expose] def system (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M)) : PatchSystem b :=
  Classical.choice (exists_system b forward backward)

end LeanShared.HyperbolicAdaptedPatchSystem
