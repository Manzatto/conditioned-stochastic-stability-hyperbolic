module
public import LeanShared.Dynamics.ReversedHyperbolicBasicSet

/-! Reversal preserves the literal compact isolated basic set and its dense
bilateral orbit, including endpoint stable/unstable dimensions. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle

theorem orbit_symm {M : Type*} [MetricSpace M] (T : M ≃ₜ M) (x : M) (n : ℤ) :
    orbit T.symm x n = orbit T x (-n) := by
  by_cases zero : n = 0
  · subst n
    simp only [orbit,neg_zero,Int.toNat_zero,Function.iterate_zero,Function.id_def,ite_self]
  · by_cases nonnegative : 0 ≤ n
    · have negative : ¬ 0 ≤ -n := by omega
      simp only [orbit,ite_eq_left nonnegative,ite_eq_right negative,neg_neg]
    · have nonnegativeNeg : 0 ≤ -n := by omega
      simp only [orbit,ite_eq_right nonnegative,ite_eq_left nonnegativeNeg,Homeomorph.symm_symm]

def BasicData.reversed
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    BasicData (E := E) T.symm Λ V := by
  refine {
    hyperbolic := b.hyperbolic.reversed forward inverse
    nonempty := b.nonempty
    open_neighborhood := b.open_neighborhood
    subset_neighborhood := b.subset_neighborhood
    isolated := ?_
    dense_orbit := ?_ }
  · simpa only [LeanShared.ReversibleTransitivity.isolatedCore_symm] using b.isolated
  · obtain ⟨x,hx,dense⟩ := b.dense_orbit
    refine ⟨x,hx,?_⟩
    have ranges : range (orbit T.symm x) = range (orbit T x) := by
      ext y
      constructor
      · rintro ⟨n,rfl⟩
        exact ⟨-n,(orbit_symm T x n).symm⟩
      · rintro ⟨n,rfl⟩
        exact ⟨-n,by simpa only [neg_neg] using orbit_symm T x (-n)⟩
    rw [ranges]
    exact dense

end LeanShared.HyperbolicBasicSet
