module
public import LeanShared.Dynamics.BasicHyperbolicShadowing
public import LeanShared.Dynamics.FinitePseudoOrbitExtension
public import LeanShared.Dynamics.InvariantCoreHomeomorphism

/-! A single tolerance shadows arbitrary finite pseudo-orbits in the basic
set, independently of their length. Entire extensions are constructed by
genuine orbits, and the shadowing point remains in the basic set. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff

theorem BasicData.finite_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (ε:ℝ) (positiveε:0<ε) :
    ∃η:ℝ,0<η ∧ ∀n:ℕ,∀p:Fin (n+1)→Λ,
      (∀j:ℕ,∀hj:j<n,
        dist (T (p ⟨j+1,by omega⟩).val) (p ⟨j,by omega⟩).val<η) →
      ∃orbit:ℤ→Λ,(∀j,T (orbit (j+1)).val=(orbit j).val) ∧
        ∀j:Fin (n+1),dist (orbit (j.val:ℤ)).val (p j).val<ε := by
  obtain ⟨η,positiveη,shadow⟩ := b.bilateral_shadowing forward inverse ε positiveε
  let S:=invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  refine ⟨η,positiveη,fun n p pseudo=>?_⟩
  let reference:=FinitePseudoOrbitExtension.reference S p
  have step (j:ℤ) : dist (T (reference (j+1)).val) (reference j).val<η :=
    FinitePseudoOrbitExtension.step_bound S p η positiveη pseudo j
  obtain ⟨orbit,orbitStep,close⟩ := shadow reference step
  refine ⟨orbit,orbitStep,fun j=>?_⟩
  have same : reference (j.val:ℤ)=p j := FinitePseudoOrbitExtension.prefix_agreement S p j
  simpa only [same] using close (j.val:ℤ)

end LeanShared.HyperbolicBasicSet
