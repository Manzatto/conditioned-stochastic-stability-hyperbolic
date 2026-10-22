module

public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import LeanShared.Dynamics.StrictTrappingBasicPartition

/-! The actual Axiom A periodic-density hypothesis supplies the absorbing
basic-set partition. Only density of the chosen integer orbit is used for
each basic set; no forward-transitivity assumption is introduced. -/

public noncomputable section
open Set Function Bundle
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.PeriodicDenseBasicPartition

theorem periodic_mem_image_absorber {X : Type*} (T : X → X) {A : Set X}
    (forward : MapsTo T A A) {x : X} (periodic : x ∈ periodicPts T)
    (enters : T x ∈ A) : x ∈ T '' A := by
  obtain ⟨n, positive, returns⟩ := periodic
  have equation : T^[n] x = x := returns
  have count : (n-1).succ = n := by omega
  have member : x ∈ A := by
    have inside := forward.iterate (n-1) enters
    rw [← iterate_succ_apply T (n-1) x, count, equation] at inside
    exact inside
  refine ⟨T^[n-1] x, forward.iterate (n-1) member, ?_⟩
  rw [← iterate_succ_apply' T (n-1) x, count]
  exact equation

theorem closure_periodic_mem_absorber_of_image_mem {X : Type*} [TopologicalSpace X]
    (T : X ≃ₜ X) {A : Set X} (openA : IsOpen A)
    (strict : MapsTo T (closure A) A) {x : X}
    (dense : x ∈ closure (periodicPts (T : X → X))) (enters : T x ∈ A) : x ∈ A := by
  have forward : MapsTo T A A := fun _ hx => strict (subset_closure hx)
  have inClosure : x ∈ closure (T '' A) := by
    apply mem_closure_iff.mpr
    intro U openU member
    obtain ⟨p, hp, periodic⟩ := mem_closure_iff.mp dense (U ∩ T ⁻¹' A)
      (openU.inter (openA.preimage T.continuous)) ⟨member, enters⟩
    exact ⟨p, hp.1, periodic_mem_image_absorber T forward periodic hp.2⟩
  have inside : closure (T '' A) ⊆ T '' closure A :=
    closure_minimal (image_mono subset_closure) (T.isClosedMap _ isClosed_closure)
  obtain ⟨y, hy, rfl⟩ := inside inClosure
  exact strict hy

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem dichotomy (periodic_dense : closure (periodicPts (T : M → M)) = Paper.nonwanderingSet T)
    (A : Set M) (openA : IsOpen A) (strict : MapsTo T (closure A) A) (i : Fin D.count) :
    D.core i ⊆ A ∨ D.core i ⊆ interior Aᶜ := by
  have dense (x : M) (hx : x ∈ D.core i) : x ∈ closure (periodicPts (T : M → M)) := by
    rw [periodic_dense, ← D.covering]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have forwardCore : MapsTo T (D.core i) (D.core i) := by
    intro x hx
    exact (D.basic i).hyperbolic.invariant ▸ mem_image_of_mem T hx
  have backwardCore : MapsTo T.symm (D.core i) (D.core i) := by
    intro x hx
    obtain ⟨y, hy, same⟩ := (D.basic i).hyperbolic.invariant.symm ▸ hx
    simpa only [← same, T.symm_apply_apply] using hy
  have forwardA : MapsTo T A A := fun _ hx => strict (subset_closure hx)
  have backwardA : MapsTo T.symm (D.core i ∩ A) (D.core i ∩ A) := by
    intro x hx
    refine ⟨backwardCore hx.1, closure_periodic_mem_absorber_of_image_mem T openA strict
      (dense _ (backwardCore hx.1)) ?_⟩
    simpa only [T.apply_symm_apply] using hx.2
  obtain ⟨x, hx, orbitDense⟩ := (D.basic i).dense_orbit
  by_cases absorbed : x ∈ A
  · apply Or.inl
    have orbitInside : range (LeanShared.HyperbolicBasicSet.orbit T x) ⊆ A := by
      rintro y ⟨n, rfl⟩
      unfold LeanShared.HyperbolicBasicSet.orbit
      split
      · exact forwardA.iterate n.toNat absorbed
      · exact (backwardA.iterate (-n).toNat ⟨hx, absorbed⟩).2
    intro y hy
    have inClosure := (closure_mono orbitInside) (orbitDense hy)
    exact closure_periodic_mem_absorber_of_image_mem T openA strict (dense y hy) (strict inClosure)
  · have forwardLive : MapsTo T (D.core i ∩ Aᶜ) (D.core i ∩ Aᶜ) := by
      intro y hy
      refine ⟨forwardCore hy.1, ?_⟩
      exact fun enters => hy.2 (closure_periodic_mem_absorber_of_image_mem T openA strict
        (dense y hy.1) enters)
    have backwardLive : MapsTo T.symm (D.core i ∩ Aᶜ) (D.core i ∩ Aᶜ) := by
      intro y hy
      refine ⟨backwardCore hy.1, ?_⟩
      intro enters
      have hit := forwardA enters
      exact hy.2 (by simpa only [T.apply_symm_apply] using hit)
    have orbitOutside : range (LeanShared.HyperbolicBasicSet.orbit T x) ⊆ Aᶜ := by
      rintro y ⟨n, rfl⟩
      unfold LeanShared.HyperbolicBasicSet.orbit
      split
      · exact (forwardLive.iterate n.toNat ⟨hx, absorbed⟩).2
      · exact (backwardLive.iterate (-n).toNat ⟨hx, absorbed⟩).2
    have live : D.core i ⊆ Aᶜ :=
      orbitDense.trans (closure_minimal orbitOutside openA.isClosed_compl)
    apply Or.inr
    apply LeanShared.invariant_subset_interior_live_of_strict_trapping T A (D.core i)
      (by rintro y ⟨z, hz, rfl⟩; exact strict hz)
      (by rintro y ⟨z, hz, rfl⟩; exact forwardCore hz)
    exact Set.disjoint_left.mpr (fun y hy ha => live hy ha)

end ConditionedStochasticStabilityHyperbolic.Global.PeriodicDenseBasicPartition
