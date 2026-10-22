module
public import LeanShared.Dynamics.BasicHyperbolicFiniteShadowing
public import LeanShared.Dynamics.CompactMixingChains
public import LeanShared.Dynamics.FiniteOrbitWordAssembly
import all LeanShared.Dynamics.FiniteOrbitWordAssembly

/-! A single gap, chosen before the number and lengths of orbit segments,
lets an actual orbit in the basic set trace every prescribed segment.
Times are written in the backward indexing of the bilateral solver. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open FiniteOrbitWordAssembly BilateralHomeomorphismOrbit

theorem BasicData.backward_specification
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (mixing:MixingOn T Λ) (ε:ℝ) (positiveε:0<ε) :
    ∃gap:ℕ,0<gap ∧ ∀length:ℕ→ℕ,∀points:ℕ→Λ,∀k:ℕ,
      ∃p:ℤ→Λ,(∀j,T (p (j+1)).val=(p j).val) ∧
        ∀i≤k,∀j≤length i,
          dist (p ((offset gap length i+j:ℕ):ℤ)).val
            (((T.symm:M→M)^[j]) (points i).val)<ε := by
  obtain ⟨η,positiveη,shadow⟩ := b.finite_shadowing forward inverse ε positiveε
  obtain ⟨gap,positiveGap,chains⟩ := mixing.uniform_chains b.hyperbolic.compact b.hyperbolic.invariant η positiveη
  let S:=invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have nativeChains (x y:Λ) : ∃p:Fin (gap+1)→Λ,
      p ⟨0,by omega⟩=x ∧ p ⟨gap,by omega⟩=y ∧
      ∀j:ℕ,∀hj:j<gap,dist (S (p ⟨j+1,by omega⟩)) (p ⟨j,by omega⟩)<η := chains x y
  have reverseEquivariant : Function.Semiconj (Subtype.val:Λ→M) S.symm T.symm := fun _=>rfl
  refine ⟨gap,positiveGap,fun length points k=>?_⟩
  obtain ⟨word,trace,wordStep⟩ := assemble S η positiveη gap positiveGap nativeChains length points k
  obtain ⟨p,pStep,pClose⟩ := shadow (ending gap length k) word wordStep
  refine ⟨p,pStep,fun i hi j hj=>?_⟩
  have bound:offset gap length i+j≤ending gap length k :=
    (Nat.add_le_add_left hj _).trans (end_le gap length hi)
  have close := pClose (⟨offset gap length i+j,by omega⟩:Fin (ending gap length k+1))
  have same := trace i hi j hj
  have segment : (BilateralHomeomorphismOrbit.orbit S (points i) (j:ℤ)).val=((T.symm:M→M)^[j]) (points i).val := by
    rw [nat_time]
    exact (reverseEquivariant.iterate_right j).eq (points i)
  rw [same,segment] at close
  exact close

end LeanShared.HyperbolicBasicSet
