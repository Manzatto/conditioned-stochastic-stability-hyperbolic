module
public import LeanShared.Geometry.LinearRechartedRiemannian
public import LeanShared.Geometry.DiffeomorphismIterates
public import LeanShared.Dynamics.HyperbolicBasicSet

/-! Actual uniformly hyperbolic tangent data transported to linearly
recharted coordinates. The supplied tangent metric is transported by an
exact fiber isometry, so the contraction constants are unchanged. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicLinearRechart
open HyperbolicBasicSet LinearRechartedManifold
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  (e : E ≃L[ℝ] F) {T : M ≃ₜ M} {Λ V : Set M}

@[expose] def transport (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    HyperbolicData (E := F) T Λ := by
  rcases h with ⟨compact, invariant, stable, unstable, complementary, projection,
    projection_range, projection_kernel, projection_idempotent, continuous_splitting,
    stable_invariant, unstable_invariant, constant, contraction, constant_pos,
    contraction_pos, contraction_lt_one, stable_bound, unstable_bound⟩
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let oldNorm := fun (x : M) (v : TangentSpace (𝓘(ℝ,E)) x) => ‖v‖
  letI := charts (M := M) e
  letI := manifold (M := M) e
  let j := identityDifferential (M := M) e
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  have norms (x : M) (v : TangentSpace (𝓘(ℝ,E)) x) :
      ‖j x v‖ = oldNorm x v := transportMetric_norm e original x v
  have derivatives {f : M → M}
      (hf : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f)
      (x : M) (v : TangentSpace (𝓘(ℝ,F)) x) :
      mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) f x v =
        j (f x) (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x ((j x).symm v)) := by
    have identity := congrArg
      (fun l => l ((j x).symm v)) (mfderiv_rechart_comp e hf x)
    simpa only [j, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using identity
  have invariance (s : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x))
      (hs : ∀ x ∈ Λ, (s x).map
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap = s (T x)) :
      ∀ x ∈ Λ, ((s x).map (j x).toLinearMap).map
        (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) T x).toLinearMap =
        (s (T x)).map (j (T x)).toLinearMap := by
    intro x hx
    rw [← Submodule.map_comp, ← hs x hx, ← Submodule.map_comp]
    congr 1
    ext v
    have identity := congrArg (fun l => l v) (mfderiv_rechart_comp e forward x)
    exact identity
  refine {
    compact := compact
    invariant := invariant
    stable := fun x => (stable x).map (j x).toLinearMap
    unstable := fun x => (unstable x).map (j x).toLinearMap
    complementary := fun x hx =>
      (Submodule.orderIsoMapComap (j x).toLinearEquiv).isCompl_iff.mp (complementary x hx)
    projection := fun x => (j x).toContinuousLinearMap.comp
      ((projection x).comp (j x).symm.toContinuousLinearMap)
    projection_range := ?_
    projection_kernel := ?_
    projection_idempotent := ?_
    continuous_splitting := ?_
    stable_invariant := invariance stable stable_invariant
    unstable_invariant := invariance unstable unstable_invariant
    constant := constant
    contraction := contraction
    constant_pos := constant_pos
    contraction_pos := contraction_pos
    contraction_lt_one := contraction_lt_one
    stable_bound := ?_
    unstable_bound := ?_ }
  · intro x hx
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨projection x ((j x).symm w), projection_range x hx ▸ ⟨_, rfl⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (projection_range x hx).symm ▸ hw
      exact ⟨j x u, by simp⟩
  · intro x hx
    ext v
    change j x (projection x ((j x).symm v)) = 0 ↔
      v ∈ (unstable x).map (j x).toLinearMap
    rw [map_eq_zero_iff _ (j x).injective]
    change (j x).symm v ∈ (projection x).ker ↔ _
    rw [projection_kernel x hx]
    exact (Submodule.mem_map_equiv (p := unstable x)).symm
  · intro x hx
    ext v
    have identity := congrArg (fun l => l ((j x).symm v)) (projection_idempotent x hx)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using congrArg (j x) identity
  · exact (tangentHomeomorph (M := M) e).continuous.comp_continuousOn
      (continuous_splitting.comp
        (tangentHomeomorph (M := M) e).symm.continuous.continuousOn
        (fun _ hx => hx))
  · intro n x hx v hv
    have hv' : (j x).symm v ∈ stable x :=
      (Submodule.mem_map_equiv (p := stable x)).mp hv
    rw [derivatives (DiffeomorphismIterates.mdifferentiable_iterate T forward n), norms]
    have bound := stable_bound n x hx ((j x).symm v) hv'
    change oldNorm _ _ ≤ constant * contraction ^ n * oldNorm x ((j x).symm v) at bound
    simpa only [← norms, ContinuousLinearEquiv.apply_symm_apply] using bound
  · intro n x hx v hv
    have hv' : (j x).symm v ∈ unstable x :=
      (Submodule.mem_map_equiv (p := unstable x)).mp hv
    rw [derivatives (DiffeomorphismIterates.mdifferentiable_iterate T.symm inverse n), norms]
    have bound := unstable_bound n x hx ((j x).symm v) hv'
    change oldNorm _ _ ≤ constant * contraction ^ n * oldNorm x ((j x).symm v) at bound
    simpa only [← norms, ContinuousLinearEquiv.apply_symm_apply] using bound


/-- The actual basic set, map, neighborhood and orbit remain unchanged. -/
@[expose] def transportBasic (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    BasicData (E := F) T Λ V := by
  rcases b with ⟨hyperbolic, nonempty, open_neighborhood, subset_neighborhood,
    isolated, dense_orbit⟩
  let transported := transport e hyperbolic forward inverse
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  letI := charts (M := M) e
  letI := manifold (M := M) e
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  exact {
    hyperbolic := transported
    nonempty := nonempty
    open_neighborhood := open_neighborhood
    subset_neighborhood := subset_neighborhood
    isolated := isolated
    dense_orbit := dense_orbit }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem transport_unstable (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    let oldUnstable := h.unstable;
    let transported := transport e h forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.unstable = fun x => (oldUnstable x).map
      (identityDifferential e x).toLinearMap := by
  cases h
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem transport_stable (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    let oldStable := h.stable;
    let transported := transport e h forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.stable = fun x => (oldStable x).map
      (identityDifferential e x).toLinearMap := by
  cases h
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem transport_contraction (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    let oldContraction := h.contraction;
    let transported := transport e h forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.contraction = oldContraction := by
  cases h
  rfl

omit [FiniteDimensional ℝ E] in
/-- Continuity of the supplied tangent metric is retained by the actual
model change, rather than supplied as a new hypothesis. -/
theorem continuous_metric
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] :
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    IsContinuousRiemannianBundle F (fun x : M => TangentSpace (𝓘(ℝ,F)) x) := by
  let g := CompactRiemannianMetricComparison.continuousMetricOfBundle
    (F := E) (fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  exact ⟨⟨(transportMetric e original).inner,
    continuous_transportMetric e g, fun x v w => rfl⟩⟩

end LeanShared.HyperbolicLinearRechart
