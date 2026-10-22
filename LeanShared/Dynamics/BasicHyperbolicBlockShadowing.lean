module
public import LeanShared.Dynamics.HyperbolicPseudoOrbitShadowing
public import LeanShared.Dynamics.HyperbolicIsometricFraming

/-! Literal hyperbolic basic data produce a fixed iterate with bilateral
manifold shadowing. All coherent charts and tangent frames are constructed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff

theorem BasicData.exists_block_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    ∃N:ℕ,0<N ∧ ∀ε:ℝ,0<ε → ∃η:ℝ,0<η ∧ ∀reference:ℤ→Λ,
      (∀n,dist ((T^N) (reference (n+1)).val) (reference n).val<η) →
      ∃orbit:ℤ→M,(∀n,(T^N) (orbit (n+1))=orbit n) ∧
        ∀n,dist (orbit n) (reference n).val<ε := by
  obtain ⟨d⟩ := b.hyperbolic.exists_pseudo_reference_geometry
    (forward.mdifferentiable one_ne_zero) inverse
  obtain ⟨a⟩ := b.exists_isometricFraming (forward.mdifferentiable one_ne_zero) inverse
  exact ⟨d.blockLength,d.block_positive,
    fun ε hε=>HyperbolicData.pseudo_reference_shadowing d a forward ε hε⟩

end LeanShared.HyperbolicBasicSet
