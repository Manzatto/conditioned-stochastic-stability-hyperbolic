module
public import LeanShared.Dynamics.HyperbolicAdaptedPatchSystem
public import LeanShared.Dynamics.HyperbolicAdaptedOneStepBlocks

/-! The already chosen adapted time is retained when obtaining actual
one-step blocks. No second existential choice of an adapted norm is made. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedForms
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem PatchSystem.one_step_blocks (system : PatchSystem b)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (x : M) (hx : x ∈ Λ) (ds du : ℕ)
    (es : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] b.hyperbolic.stable x)
    (fs : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] b.hyperbolic.stable (T x))
    (eu : EuclideanSpace ℝ (Fin du) ≃L[ℝ] b.hyperbolic.unstable x)
    (fu : EuclideanSpace ℝ (Fin du) ≃L[ℝ] b.hyperbolic.unstable (T x))
    (normEs : ∀ v, splitForm T T.symm b.hyperbolic.projection system.rate system.time x
      (es v).val (es v).val = ‖v‖ ^ 2)
    (normFs : ∀ v, splitForm T T.symm b.hyperbolic.projection system.rate system.time (T x)
      (fs v).val (fs v).val = ‖v‖ ^ 2)
    (normEu : ∀ v, splitForm T T.symm b.hyperbolic.projection system.rate system.time x
      (eu v).val (eu v).val = ‖v‖ ^ 2)
    (normFu : ∀ v, splitForm T T.symm b.hyperbolic.projection system.rate system.time (T x)
      (fu v).val (fu v).val = ‖v‖ ^ 2) :
    ∃ S : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] EuclideanSpace ℝ (Fin ds),
    ∃ U : EuclideanSpace ℝ (Fin du) ≃L[ℝ] EuclideanSpace ℝ (Fin du),
      ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
      (∀ v, (fs (S v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x (es v).val) ∧
      (∀ v, (fu (U v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x (eu v).val) ∧
      (∀ v, (eu (U.symm v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm (T x) (fu v).val) := by
  obtain ⟨S, U, actionS, actionU, actionInv⟩ := b.hyperbolic.actual_one_step_tangent_blocks
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) x hx
  let form (y : M) (V : Submodule ℝ (TangentSpace (𝓘(ℝ, E)) y)) :=
    (splitForm T T.symm b.hyperbolic.projection system.rate system.time y).bilinearComp V.subtypeL V.subtypeL
  have nonnegative : 0 ≤ system.rate := system.rate_pos.le
  have stableEstimate (v : b.hyperbolic.stable x) :
      form (T x) (b.hyperbolic.stable (T x)) (S v) (S v) ≤ system.rate ^ 2 * form x (b.hyperbolic.stable x) v v := by
    change splitForm T T.symm b.hyperbolic.projection system.rate system.time (T x) (S v).val (S v).val ≤ _
    rw [actionS]
    exact system.stable_step x hx v.val v.property
  have targetInside : T x ∈ Λ := b.hyperbolic.invariant ▸ mem_image_of_mem T hx
  have inverseEstimate (v : b.hyperbolic.unstable (T x)) :
      form x (b.hyperbolic.unstable x) (U.symm v) (U.symm v) ≤
        system.rate ^ 2 * form (T x) (b.hyperbolic.unstable (T x)) v v := by
    change splitForm T T.symm b.hyperbolic.projection system.rate system.time x (U.symm v).val (U.symm v).val ≤
      system.rate ^ 2 * splitForm T T.symm b.hyperbolic.projection system.rate system.time (T x) v.val v.val
    rw [actionInv]
    have estimate := system.unstable_step (T x) targetInside v.val v.property
    have changeBase (y : M) (equal : y = x) (w : TangentSpace (𝓘(ℝ, E)) y) :
        splitForm T T.symm b.hyperbolic.projection system.rate system.time y w w =
          splitForm T T.symm b.hyperbolic.projection system.rate system.time x
            (show TangentSpace (𝓘(ℝ, E)) x from w)
            (show TangentSpace (𝓘(ℝ, E)) x from w) := by
      subst y
      rfl
    rw [changeBase _ (T.symm_apply_apply x) _] at estimate
    exact estimate
  refine ⟨(es.trans S).trans fs.symm, (eu.trans U).trans fu.symm,
    BilinearCoordinateContraction.bound (form x (b.hyperbolic.stable x))
      (form (T x) (b.hyperbolic.stable (T x))) es fs S normEs normFs system.rate nonnegative stableEstimate,
    ?_, ?_, ?_, ?_⟩
  · exact BilinearCoordinateContraction.bound (form (T x) (b.hyperbolic.unstable (T x)))
      (form x (b.hyperbolic.unstable x)) fu eu U.symm normFu normEu system.rate nonnegative inverseEstimate
  · intro v
    change (fs (fs.symm (S (es v)))).val = _
    rw [fs.apply_symm_apply, actionS]
  · intro v
    change (fu (fu.symm (U (eu v)))).val = _
    rw [fu.apply_symm_apply, actionU]
  · intro v
    change (eu (eu.symm (U.symm (fu v)))).val = _
    rw [eu.apply_symm_apply, actionInv]

end LeanShared.HyperbolicAdaptedPatchSystem
