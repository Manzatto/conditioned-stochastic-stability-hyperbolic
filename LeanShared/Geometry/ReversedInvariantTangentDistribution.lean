module
public import LeanShared.Geometry.DiffeomorphismInverseDifferential
public import LeanShared.Geometry.InvariantTangentBlockEquivalence

/-! Exact reversal of an invariant tangent distribution for a genuine
differentiable diffeomorphism. Inverse invariance is proved from the actual
forward differential and its inverse, rather than supplied separately. -/
public noncomputable section
namespace LeanShared.ReversedInvariantTangentDistribution
open Set IsManifold
open scoped Manifold

theorem invariant
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (T : M ≃ₜ M) (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (K : Set M) (invariantK : T '' K = K)
    (S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x))
    (invariantS : ∀ x ∈ K,
      (S x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = S (T x)) :
    ∀ x ∈ K, (S x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x).toLinearMap = S (T.symm x) := by
  intro x hx
  have inverseInside : T.symm x ∈ K := by
    obtain ⟨y,hy,equal⟩ := invariantK.symm ▸ hx
    simpa only [← equal,Homeomorph.symm_apply_apply] using hy
  have preserves : MapsTo T K K := fun y hy => invariantK ▸ mem_image_of_mem T hy
  have existence : ∃ A : S (T.symm x) ≃L[ℝ] S x,
      ∀ v, (A.symm v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v.val := by
    have raw := InvariantTangentDistributionIterates.exists_block_equivalence
      T forward inverse K preserves S invariantS 1 (T.symm x) inverseInside
    rw [pow_one] at raw
    generalize equation : T.symm x = y at raw
    have image : T y = x := by rw [← equation, Homeomorph.apply_symm_apply]
    subst x
    obtain ⟨A,_action,inverseAction⟩ := raw
    exact ⟨A,inverseAction⟩
  obtain ⟨A,inverseAction⟩ := existence
  apply le_antisymm
  · rintro y ⟨v,hv,rfl⟩
    have member := (A.symm ⟨v,hv⟩).property
    rw [inverseAction] at member
    exact member
  · intro y hy
    refine ⟨(A ⟨y,hy⟩).val,(A ⟨y,hy⟩).property,?_⟩
    have equality := congrArg Subtype.val (A.symm_apply_apply ⟨y,hy⟩)
    rw [inverseAction] at equality
    exact equality

end LeanShared.ReversedInvariantTangentDistribution
