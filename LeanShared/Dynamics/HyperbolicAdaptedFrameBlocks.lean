module
public import LeanShared.Dynamics.HyperbolicAdaptedPatchBlocks
public import LeanShared.Dynamics.HyperbolicAdaptedReferenceFrames

/-! Exact diagonal action of the original one-step tangent map in the
actual local adapted whole frames, with the already chosen norm and rate. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedFramePatches
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

@[expose] def forwardPoint (base : BasicData (E := E) T Λ V) (x : Λ) : Λ :=
  ⟨T x.val, base.hyperbolic.invariant.subset (mem_image_of_mem T x.property)⟩

theorem PatchSystem.actual_frame_blocks (system : PatchSystem b)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (c d x : Λ) (hx : x ∈ system.frameDomain c)
    (ht : forwardPoint b x ∈
      system.frameDomain d) :
    let e := system.referenceFrame c ⟨x, hx⟩
    let f := system.referenceFrame d
      ⟨forwardPoint b x, ht⟩
    ∃ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
        EuclideanSpace ℝ (Fin system.framing.stableDimension),
    ∃ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
        EuclideanSpace ℝ (Fin system.framing.unstableDimension),
      ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
      f.symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val).comp e.toContinuousLinearMap) =
          U.toContinuousLinearMap.prodMap S.toContinuousLinearMap := by
  let es : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ] b.hyperbolic.stable x.val := (system.stableFrame c).euclideanCoordinates ⟨x.val, x.property, hx.1.2⟩
  let eu : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ] b.hyperbolic.unstable x.val := (system.unstableFrame c).euclideanCoordinates ⟨x.val, x.property, hx.1.1⟩
  have target : T x.val ∈ Λ := (forwardPoint b x).property
  let fs : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ] b.hyperbolic.stable (T x.val) := (system.stableFrame d).euclideanCoordinates ⟨T x.val, target, ht.1.2⟩
  let fu : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ] b.hyperbolic.unstable (T x.val) := (system.unstableFrame d).euclideanCoordinates ⟨T x.val, target, ht.1.1⟩
  have normEs (v) : HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection
      system.rate system.time x.val (es v).val (es v).val = ‖v‖ ^ 2 :=
    (system.stableFrame c).euclidean_quadratic ⟨x.val, x.property, hx.1.2⟩ v
  have normFs (v) : HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection
      system.rate system.time (T x.val) (fs v).val (fs v).val = ‖v‖ ^ 2 :=
    (system.stableFrame d).euclidean_quadratic ⟨T x.val, target, ht.1.2⟩ v
  have normEu (v) : HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection
      system.rate system.time x.val (eu v).val (eu v).val = ‖v‖ ^ 2 :=
    (system.unstableFrame c).euclidean_quadratic ⟨x.val, x.property, hx.1.1⟩ v
  have normFu (v) : HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection
      system.rate system.time (T x.val) (fu v).val (fu v).val = ‖v‖ ^ 2 :=
    (system.unstableFrame d).euclidean_quadratic ⟨T x.val, target, ht.1.1⟩ v
  have blocks := PatchSystem.one_step_blocks (b := b) system forward backward x.val x.property
    system.framing.stableDimension system.framing.unstableDimension es fs eu fu
  obtain ⟨S, U, boundS, boundU, actionS, actionU, _⟩ := blocks normEs normFs normEu normFu
  refine ⟨S, U, boundS, boundU, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply (system.referenceFrame d ⟨⟨T x.val, target⟩, ht⟩).injective
  change (system.referenceFrame d ⟨⟨T x.val, target⟩, ht⟩)
      ((system.referenceFrame d ⟨⟨T x.val, target⟩, ht⟩).symm
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val
          (system.referenceFrame c ⟨x, hx⟩ v))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val
    ((eu v.1).val + (es v.2).val) = (fu (U v.1)).val + (fs (S v.2)).val
  rw [map_add, actionU, actionS]

end LeanShared.HyperbolicAdaptedPatchSystem
