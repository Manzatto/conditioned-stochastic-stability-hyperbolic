module
public import LeanShared.Dynamics.HyperbolicAdaptedFrameCoordinates
public import LeanShared.Dynamics.HyperbolicAdaptedContraction
public import Mathlib.LinearAlgebra.Projection

/-! Whole adapted coordinate frames, unstable first, for the original
tangent norm. Their bounds are independent of the local patch and point. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedFramePatches
open HyperbolicAdaptedForms HyperbolicBasicSet HyperbolicAdaptedContraction HyperbolicFiniteAdaptedEnergy
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
  {a : ℝ} {N ds du : ℕ} {x : Λ}

@[expose] def LocalFrame.euclideanCoordinates
    {S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)} {d : ℕ}
    (F : LocalFrame h S d a N x) (y : ↥(Λ ∩ F.neighborhood)) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] S y.val :=
  ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).trans
    (F.coordinates y).toLinearEquiv).toContinuousLinearEquiv

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem LocalFrame.euclidean_quadratic
    {S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)} {d : ℕ}
    (F : LocalFrame h S d a N x) (y : ↥(Λ ∩ F.neighborhood))
    (c : EuclideanSpace ℝ (Fin d)) :
    splitForm T T.symm h.projection a N y.val
      (F.euclideanCoordinates y c).val (F.euclideanCoordinates y c).val = ‖c‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact F.quadratic y (fun i => c i)

@[expose] def wholeFrame (Fu : LocalFrame h h.unstable du a N x)
    (Fs : LocalFrame h h.stable ds a N x)
    (y : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood))) :
    (EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) ≃L[ℝ]
      TangentSpace (𝓘(ℝ, E)) y.val :=
  (((Fu.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.1⟩).toLinearEquiv.prodCongr
    (Fs.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.2⟩).toLinearEquiv).trans
      ((h.unstable y.val).prodEquivOfIsCompl (h.stable y.val)
        (h.complementary y.val y.property.1).symm)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem wholeFrame_apply (Fu : LocalFrame h h.unstable du a N x)
    (Fs : LocalFrame h h.stable ds a N x)
    (y : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood)))
    (z : EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) :
    wholeFrame Fu Fs y z =
      (Fu.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.1⟩ z.1).val +
      (Fs.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.2⟩ z.2).val := rfl

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem wholeFrame_quadratic (Fu : LocalFrame h h.unstable du a N x)
    (Fs : LocalFrame h h.stable ds a N x)
    (y : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood)))
    (z : EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) :
    splitForm T T.symm h.projection a N y.val
      (wholeFrame Fu Fs y z) (wholeFrame Fu Fs y z) = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  let u := Fu.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.1⟩ z.1
  let s := Fs.euclideanCoordinates ⟨y.val, y.property.1, y.property.2.2⟩ z.2
  have normU : splitForm T T.symm h.projection a N y.val u.val u.val = ‖z.1‖ ^ 2 :=
    Fu.euclidean_quadratic ⟨y.val, y.property.1, y.property.2.1⟩ z.1
  have normS : splitForm T T.symm h.projection a N y.val s.val s.val = ‖z.2‖ ^ 2 :=
    Fs.euclidean_quadratic ⟨y.val, y.property.1, y.property.2.2⟩ z.2
  have pu := projection_unstable h y.val y.property.1 u.val u.property
  have ps := projection_stable h y.val y.property.1 s.val s.property
  have subtract : (u.val + s.val) - s.val = u.val := add_sub_cancel_right _ _
  rw [wholeFrame_apply, splitForm_self]
  change iterateEnergy T a N y.val (h.projection y.val (u.val + s.val)) +
    iterateEnergy T.symm a N y.val ((u.val + s.val) - h.projection y.val (u.val + s.val)) = _
  rw [map_add, pu, ps, zero_add, subtract,
    ← stable_self h a N y.val y.property.1 s.val s.property,
    ← unstable_self h a N y.val y.property.1 u.val u.property,
    normS, normU, add_comm]

/-- Uniform bounds for whole frame maps and their inverses, measured in
the original tangent metric and the fixed product Euclidean model. -/
theorem wholeFrame_uniform_bounds (h : HyperbolicData (E := E) T Λ)
    (a : ℝ) (N : ℕ) (length : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (du ds : ℕ) (x : Λ)
      (Fu : LocalFrame h h.unstable du a N x) (Fs : LocalFrame h h.stable ds a N x)
      (y : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood))),
      ‖(wholeFrame Fu Fs y).toContinuousLinearMap‖ ≤ 2 ∧
        ‖(wholeFrame Fu Fs y).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨B, positiveB, comparison⟩ :=
    HyperbolicAdaptedUniformComparison.uniform_comparison h a N length
  refine ⟨B + 1, by positivity, ?_⟩
  intro du ds x Fu Fs y
  let F := wholeFrame Fu Fs y
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    have lower := (comparison y.val y.property.1 (F z)).1
    rw [wholeFrame_quadratic] at lower
    have first := pow_le_pow_left₀ (norm_nonneg z.1) (norm_fst_le z) 2
    have second := pow_le_pow_left₀ (norm_nonneg z.2) (norm_snd_le z) 2
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg z))).mp
    change ‖F z‖ ^ 2 ≤ (2 * ‖z‖) ^ 2
    nlinarith
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    let z := F.symm v
    have upper := (comparison y.val y.property.1 v).2
    have quadratic := wholeFrame_quadratic Fu Fs y z
    change splitForm T T.symm h.projection a N y.val (F z) (F z) = _ at quadratic
    rw [show F z = v from F.apply_symm_apply v] at quadratic
    rw [quadratic] at upper
    have scalar : B ≤ (B + 1) ^ 2 := by nlinarith
    have large := upper.trans (mul_le_mul_of_nonneg_right scalar (sq_nonneg ‖v‖))
    change ‖z‖ ≤ (B + 1) * ‖v‖
    rw [Prod.norm_def]
    apply max_le
    · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg v))).mp
      nlinarith [sq_nonneg ‖z.2‖]
    · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg v))).mp
      nlinarith [sq_nonneg ‖z.1‖]

end LeanShared.HyperbolicAdaptedFramePatches
