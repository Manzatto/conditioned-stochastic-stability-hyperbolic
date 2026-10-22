module

public import LeanShared.Dynamics.ShiftedFiltration
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Literal strata and their closed-layer analytic regions

Adapted compact positive levels give the same isolated core in the Borel
stratum and its closure, and that core lies in the stratum interior. The
closure adds only the lower positive level's boundary. The first stratum,
whose lower level is the open absorbing A, is already closed: no volume-null
assumption on the boundary of A is needed.
-/

@[expose] public noncomputable section
open Set Function MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.FiltrationLayerGeometry
open LeanShared
variable {X : Type*} [TopologicalSpace X]

/-- Taking the closure can add lower-boundary points, but no point from
the interior of the lower level. -/
theorem closure_stratum_subset (K L : Set X) (hK : IsClosed K) :
    closure (K \ L) ⊆ K ∩ (interior L)ᶜ := by
  apply closure_minimal _ (hK.inter isOpen_interior.isClosed_compl)
  intro x hx
  exact ⟨hx.1, fun hy => hx.2 (interior_subset hy)⟩

/-- Closure does not change the literal stratum's isolated core when the
lower level maps into its own interior. -/
theorem isolatedCore_closed_stratum_eq (T : X ≃ₜ X) (K L : Set X)
    (hK : IsClosed K) (hLadapt : MapsTo T L (interior L)) :
    isolatedCore T (closure (K \ L)) = isolatedCore T (K \ L) := by
  have hsub := closure_stratum_subset K L hK
  have hpoint : ∀ x ∈ isolatedCore T (closure (K \ L)), x ∈ K \ L := by
    intro x hx
    have hfirst := hsub (forwardTrapped_subset T _ hx.1)
    refine ⟨hfirst.1, ?_⟩
    intro hxL
    have hnext := hsub (forwardTrapped_subset T _ (mapsTo_isolatedCore T _ hx).1)
    exact hnext.2 (hLadapt hxL)
  ext x
  constructor
  · intro hx
    exact ⟨fun n => hpoint _ (iterate_mem_isolatedCore T _ hx n),
      fun n => hpoint _ (iterate_symm_mem_isolatedCore T _ hx n)⟩
  · intro hx
    exact ⟨fun n => subset_closure (hx.1 n), fun n => subset_closure (hx.2 n)⟩

/-- Two adapted closed positive levels put their common isolated core
strictly inside the actual stratum. -/
theorem isolatedCore_subset_interior_stratum (T : X ≃ₜ X) (K L : Set X)
    (hL : IsClosed L) (hKadapt : MapsTo T K (interior K)) :
    isolatedCore T (K \ L) ⊆ interior (K \ L) := by
  intro x hx
  have hxK : x ∈ interior K := by
    have hprev := hKadapt (hx.2 1).1
    simpa only [iterate_one, T.apply_symm_apply] using hprev
  have hxL : x ∉ L := (hx.1 0).2
  apply interior_maximal (t := interior K ∩ Lᶜ) (s := K \ L)
    (fun y hy => ⟨interior_subset hy.1, hy.2⟩)
    (isOpen_interior.inter hL.isOpen_compl)
  exact ⟨hxK, hxL⟩

/-- The only added closed-layer points belong to the lower positive
level's frontier. -/
theorem closed_stratum_extra_subset_frontier (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    closure (K \ L) \ (K \ L) ⊆ frontier L := by
  intro x hx
  have hs := closure_stratum_subset K L hK hx.1
  have hxL : x ∈ L := by
    by_contra h
    exact hx.2 ⟨hs.1, h⟩
  rw [frontier, hL.closure_eq]
  exact ⟨hxL, hs.2⟩

section Measure
variable [MeasurableSpace X]

/-- A smooth positive lower boundary's classical volume-null statement
supplies the exact null closed-layer discrepancy. -/
theorem closed_stratum_extra_measure_zero (σ : Measure X) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (hnull : σ (frontier L) = 0) :
    σ (closure (K \ L) \ (K \ L)) = 0 := by
  apply le_antisymm _ bot_le
  exact (measure_mono (closed_stratum_extra_subset_frontier K L hK hL)).trans_eq hnull

end Measure

/-- The first layer uses the open absorbing region and is already closed,
regardless of whether that region's boundary is volume-null. -/
theorem absorbing_stratum_closed (K A : Set X) (hK : IsClosed K) (hA : IsOpen A) :
    IsClosed (K \ A) := hK.inter hA.isClosed_compl

/-- Explicit retained basic-set separation gives the first core's interior
property while keeping the absorption region fixed. -/
theorem absorbing_core_subset_interior (T : X ≃ₜ X) (K A Λ : Set X)
    (hKadapt : MapsTo T K (interior K))
    (hcore : isolatedCore T (K \ A) = Λ) (hseparation : Λ ⊆ interior Aᶜ) :
    Λ ⊆ interior (K \ A) := by
  intro x hx
  have hxc : x ∈ isolatedCore T (K \ A) := hcore.symm ▸ hx
  have hxK : x ∈ interior K := by
    have hprev := hKadapt (hxc.2 1).1
    simpa only [iterate_one, T.apply_symm_apply] using hprev
  apply interior_maximal (t := interior K ∩ interior Aᶜ) (s := K \ A)
    (fun y hy => ⟨interior_subset hy.1, interior_subset hy.2⟩)
    (isOpen_interior.inter isOpen_interior)
  exact ⟨hxK, hseparation hx⟩

end ConditionedStochasticStabilityHyperbolic.Global.FiltrationLayerGeometry
