module
public import LeanShared.Dynamics.HyperbolicAdaptedContraction
public import LeanShared.Dynamics.HyperbolicOneStepTangentBlocks
public import LeanShared.Analysis.BilinearCoordinateContraction
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The original one-step differential has contracting stable and inverse
unstable blocks in any frames orthonormal for the constructed adapted form.
The adapted time selects the norm, not an iterate of the generator. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedOneStepBlocks
open HyperbolicBasicSet HyperbolicAdaptedForms
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem exists_blocks (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (slack : h.contraction < a) :
    ∃ N : ℕ, 0 < N ∧ ∀ (x : M) (_ : x ∈ Λ) (ds du : ℕ)
      (es : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] h.stable x)
      (fs : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] h.stable (T x))
      (eu : EuclideanSpace ℝ (Fin du) ≃L[ℝ] h.unstable x)
      (fu : EuclideanSpace ℝ (Fin du) ≃L[ℝ] h.unstable (T x)),
      (∀ v, splitForm T T.symm h.projection a N x (es v).val (es v).val = ‖v‖ ^ 2) →
      (∀ v, splitForm T T.symm h.projection a N (T x) (fs v).val (fs v).val = ‖v‖ ^ 2) →
      (∀ v, splitForm T T.symm h.projection a N x (eu v).val (eu v).val = ‖v‖ ^ 2) →
      (∀ v, splitForm T T.symm h.projection a N (T x) (fu v).val (fu v).val = ‖v‖ ^ 2) →
      ∃ S : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] EuclideanSpace ℝ (Fin ds),
      ∃ U : EuclideanSpace ℝ (Fin du) ≃L[ℝ] EuclideanSpace ℝ (Fin du),
        ‖S.toContinuousLinearMap‖ ≤ a ∧ ‖U.symm.toContinuousLinearMap‖ ≤ a ∧
        (∀ v, (fs (S v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x (es v).val) ∧
        (∀ v, (fu (U v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x (eu v).val) ∧
        (∀ v, (eu (U.symm v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm (T x) (fu v).val) := by
  obtain ⟨N, length, stable, unstable⟩ :=
    HyperbolicAdaptedContraction.exists_one_step h forward backward a slack
  refine ⟨N, length, ?_⟩
  intro x hx ds du es fs eu fu normEs normFs normEu normFu
  obtain ⟨S, U, actionS, actionU, actionInv⟩ := h.actual_one_step_tangent_blocks
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) x hx
  let form (y : M) (V : Submodule ℝ (TangentSpace (𝓘(ℝ, E)) y)) :=
    (splitForm T T.symm h.projection a N y).bilinearComp V.subtypeL V.subtypeL
  have nonnegative : 0 ≤ a := (h.contraction_pos.trans slack).le
  have stableEstimate (v : h.stable x) :
      form (T x) (h.stable (T x)) (S v) (S v) ≤ a ^ 2 * form x (h.stable x) v v := by
    change splitForm T T.symm h.projection a N (T x) (S v).val (S v).val ≤ _
    rw [actionS]
    exact stable x hx v.val v.property
  have targetInside : T x ∈ Λ := h.invariant ▸ mem_image_of_mem T hx
  have inverseEstimate (v : h.unstable (T x)) :
      form x (h.unstable x) (U.symm v) (U.symm v) ≤
        a ^ 2 * form (T x) (h.unstable (T x)) v v := by
    change splitForm T T.symm h.projection a N x (U.symm v).val (U.symm v).val ≤
      a ^ 2 * splitForm T T.symm h.projection a N (T x) v.val v.val
    rw [actionInv]
    have estimate := unstable (T x) targetInside v.val v.property
    have changeBase (y : M) (equal : y = x) (w : TangentSpace (𝓘(ℝ, E)) y) :
        splitForm T T.symm h.projection a N y w w =
          splitForm T T.symm h.projection a N x
            (show TangentSpace (𝓘(ℝ, E)) x from w)
            (show TangentSpace (𝓘(ℝ, E)) x from w) := by
      subst y
      rfl
    rw [changeBase _ (T.symm_apply_apply x) _] at estimate
    exact estimate
  refine ⟨(es.trans S).trans fs.symm, (eu.trans U).trans fu.symm,
    BilinearCoordinateContraction.bound (form x (h.stable x))
      (form (T x) (h.stable (T x))) es fs S normEs normFs a nonnegative stableEstimate,
    ?_, ?_, ?_, ?_⟩
  · exact BilinearCoordinateContraction.bound (form (T x) (h.unstable (T x)))
      (form x (h.unstable x)) fu eu U.symm normFu normEu a nonnegative inverseEstimate
  · intro v
    change (fs (fs.symm (S (es v)))).val = _
    rw [fs.apply_symm_apply, actionS]
  · intro v
    change (fu (fu.symm (U (eu v)))).val = _
    rw [fu.apply_symm_apply, actionU]
  · intro v
    change (eu (eu.symm (U.symm (fu v)))).val = _
    rw [eu.apply_symm_apply, actionInv]

end LeanShared.HyperbolicAdaptedOneStepBlocks
