module
public import LeanShared.Dynamics.HyperbolicBasicSet

/-! Shrinking an isolating neighborhood around the same invariant basic
set preserves the actual hyperbolic datum and dense orbit. -/
@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

def BasicData.restrictNeighborhood (b : BasicData (E := E) T Λ V)
    (O : Set M) (openO : IsOpen O) (coreO : Λ ⊆ O) (inside : O ⊆ V) :
    BasicData (E := E) T Λ O where
  hyperbolic := b.hyperbolic
  nonempty := b.nonempty
  open_neighborhood := openO
  subset_neighborhood := coreO
  isolated := by
    apply Set.Subset.antisymm
    · intro x hx
      have trapped : x ∈ isolatedCore T (closure V) := b.isolated ▸ hx
      exact ⟨fun n => subset_closure (coreO (b.isolated.symm ▸
        iterate_mem_isolatedCore T (closure V) trapped n)),
        fun n => subset_closure (coreO (b.isolated.symm ▸
          iterate_symm_mem_isolatedCore T (closure V) trapped n))⟩
    · intro x hx
      have trapped : x ∈ isolatedCore T (closure V) :=
        ⟨fun n => closure_mono inside (hx.1 n), fun n => closure_mono inside (hx.2 n)⟩
      exact b.isolated.symm ▸ trapped
  dense_orbit := b.dense_orbit

end LeanShared.HyperbolicBasicSet
