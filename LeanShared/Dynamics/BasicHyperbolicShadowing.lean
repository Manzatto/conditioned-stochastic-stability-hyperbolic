module
public import LeanShared.Dynamics.BasicHyperbolicBlockShadowing
public import LeanShared.Dynamics.IterateShadowingTransfer
public import LeanShared.Dynamics.EntireOrbitInCore
public import Mathlib.Topology.MetricSpace.Thickening

/-! Every sufficiently accurate bilateral pseudo-orbit in a hyperbolic
basic set is shadowed by an actual entire orbit IN that basic set. The
one-step tolerance, manifold charts, frames and isolated-core membership
are all derived from the literal basic data. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff

theorem BasicData.bilateral_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (ε:ℝ) (positiveε:0<ε) :
    ∃η:ℝ,0<η ∧ ∀reference:ℤ→Λ,
      (∀n,dist (T (reference (n+1)).val) (reference n).val<η) →
      ∃orbit:ℤ→Λ,(∀n,T (orbit (n+1)).val=(orbit n).val) ∧
        ∀n,dist (orbit n).val (reference n).val<ε := by
  obtain ⟨N,positiveN,blocks⟩ := b.exists_block_shadowing forward inverse
  obtain ⟨ρ,positiveρ,buffer⟩ := b.hyperbolic.compact.exists_thickening_subset_open
    b.open_neighborhood b.subset_neighborhood
  obtain ⟨η,positiveη,shadows⟩ := IterateShadowingTransfer.one_step T Λ N positiveN blocks
    (min ε ρ) (lt_min positiveε positiveρ)
  refine ⟨η,positiveη,fun reference step=>?_⟩
  obtain ⟨p,pStep,pClose⟩ := shadows reference step
  have inside (n:ℤ) : p n∈closure V := by
    apply subset_closure
    apply buffer
    exact Metric.mem_thickening_iff.mpr ⟨(reference n).val,(reference n).property,
      (pClose n).trans_le (min_le_right _ _)⟩
  have member (n:ℤ) : p n∈Λ := by
    rw [b.isolated]
    exact BilateralHomeomorphismOrbit.mem_isolatedCore T (closure V) p pStep inside n
  exact ⟨fun n=>⟨p n,member n⟩,pStep,fun n=>(pClose n).trans_le (min_le_left _ _)⟩

end LeanShared.HyperbolicBasicSet
