module
public import LeanShared.Dynamics.HyperbolicStableFibreFrames
public import LeanShared.Dynamics.HyperbolicFibreDifferential

/-! The actual stable tangent dimension of a differentiable hyperbolic basic
set is constant. Local projection frames, actual invariant differentials, and
the literal dense two-sided orbit prove the statement; no dimension/rank
constancy source is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_stable_dimension
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ ds : ℕ, ∀ x ∈ Λ, Module.finrank ℝ (b.hyperbolic.stable x) = ds := by
  let h := b.hyperbolic
  let rank : M → ℕ := fun x => Module.finrank ℝ (h.stable x)
  have preserves : MapsTo T Λ Λ := fun x hx => by
    rw [← h.invariant]
    exact mem_image_of_mem T hx
  have inversePreserves : MapsTo T.symm Λ Λ := by
    intro x hx
    have member : x ∈ T '' Λ := by rw [h.invariant]; exact hx
    obtain ⟨y, hy, image⟩ := member
    rw [← image, T.symm_apply_apply]
    exact hy
  have rankForward (x : M) (hx : x ∈ Λ) : rank (T x) = rank x := by
    obtain ⟨A, _⟩ := h.exists_stable_differential forward inverse x hx
    exact A.toLinearEquiv.finrank_eq.symm
  have rankInverse (x : M) (hx : x ∈ Λ) : rank (T.symm x) = rank x := by
    have equality := rankForward (T.symm x) (inversePreserves hx)
    simpa only [T.apply_symm_apply] using equality.symm
  have forwardIterate (x : M) (hx : x ∈ Λ) (n : ℕ) : rank ((T : M → M)^[n] x) = rank x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (rankForward _ (preserves.iterate n hx)).trans ih
  have inverseIterate (x : M) (hx : x ∈ Λ) (n : ℕ) : rank ((T.symm : M → M)^[n] x) = rank x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (rankInverse _ (inversePreserves.iterate n hx)).trans ih
  obtain ⟨x, hx, dense⟩ := b.dense_orbit
  have orbitMember (n : ℤ) : orbit T x n ∈ Λ := by
    unfold orbit
    split_ifs
    · exact preserves.iterate _ hx
    · exact inversePreserves.iterate _ hx
  have orbitRank (n : ℤ) : rank (orbit T x n) = rank x := by
    unfold orbit
    split_ifs
    · exact forwardIterate x hx _
    · exact inverseIterate x hx _
  refine ⟨rank x, fun y hy => ?_⟩
  obtain ⟨U, openU, member, equal⟩ := h.stable_finrank_locally_constant y hy
  obtain ⟨z, hzU, hzOrbit⟩ := (mem_closure_iff_nhds.mp (dense hy)) U (openU.mem_nhds member)
  obtain ⟨n, rfl⟩ := hzOrbit
  exact (equal _ ⟨orbitMember n, hzU⟩).trans (orbitRank n)

end LeanShared.HyperbolicBasicSet
