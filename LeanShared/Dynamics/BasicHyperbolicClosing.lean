module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicShadowing
public import LeanShared.Dynamics.FiniteCyclicPseudoOrbit

/-! Uniform actual periodic closing for finite near-return segments. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open BilateralHomeomorphismOrbit
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 1800000 in
theorem BasicData.closing (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ η > 0, ∀ p : ℕ, 0 < p → ∀ x ∈ Λ,
      dist ((T : M → M)^[p] x) x < η →
      ∃ z ∈ Λ, (T : M → M)^[p] z = z ∧
        ∀ j < p, dist ((T : M → M)^[j] z) ((T : M → M)^[j] x) < ε := by
  obtain ⟨η, positiveη, shadows⟩ := b.periodic_shadowing forward inverse ε positiveε
  refine ⟨η, positiveη, fun p positiveP x hx close => ?_⟩
  let _ : NeZero p := ⟨positiveP.ne'⟩
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  let word : ZMod p → Λ := fun i => ⟨(T : M → M)^[i.val] x, invariant.iterate i.val hx⟩
  let reference := FiniteCyclicPseudoOrbit.reference word
  have periodic (n : ℤ) : reference (n + (p : ℤ)) = reference n :=
    FiniteCyclicPseudoOrbit.reference_periodic word n
  have steps (n : ℤ) : dist (T (reference (n + 1)).val) (reference n).val < η := by
    exact FiniteCyclicPseudoOrbit.reference_step T (fun i => (word i).val) η
      (FiniteCyclicPseudoOrbit.orbit_word_step T p positiveP x η positiveη close) n
  obtain ⟨z, hz, fixed, near⟩ := shadows p reference periodic steps
  refine ⟨z, hz, fixed, fun j hj => ?_⟩
  have selected := near (-(j : ℤ))
  have index : ((-(-(j : ℤ)) : ℤ) : ZMod p).val = j := by
    simp only [neg_neg, Int.cast_natCast]
    exact ZMod.val_cast_of_lt hj
  simpa only [BilateralHomeomorphismOrbit.neg_nat_time, reference,
    FiniteCyclicPseudoOrbit.reference, word, index] using selected

end LeanShared.HyperbolicBasicSet
