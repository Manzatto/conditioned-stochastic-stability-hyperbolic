module

public import LeanShared.Dynamics.ControlledPlaqueClosure

/-!
# Transitivity reverses on a homeomorphism-invariant set

The forward-density definition used by the support argument is equivalent
to hitting pairs of relatively open sets. Swapping the two open sets and
cancelling iterates proves inverse transitivity. In particular, inverse
transitivity of the isolated core is derived from forward transitivity.
-/

@[expose] public section

open Set Function Filter
open scoped Topology

namespace LeanShared.ReversibleTransitivity

open ControlledPlaqueClosure

variable {X : Type*} [MetricSpace X]

/-- The support argument's density formulation is exactly the usual
open-set hitting formulation of transitivity on the relative space. -/
theorem forwardTransitiveOn_iff_hitting (f : X → X) (A : Set X) :
    forwardTransitiveOn f A ↔
      ∀ U V : Set X, IsOpen U → IsOpen V → (A ∩ U).Nonempty → (A ∩ V).Nonempty →
        ∃ n : ℕ, ∃ x ∈ A ∩ U, f^[n] x ∈ V := by
  constructor
  · intro ht U V hU hV hAU hAV
    obtain ⟨y, hyA, hyV⟩ := hAV
    obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp (ht U hU hAU hyA) V hV hyV
    obtain ⟨n, x, hx, hxn⟩ := mem_iUnion.mp hz
    exact ⟨n, x, hx, hxn ▸ hzV⟩
  · intro hh U hU hAU y hy
    apply mem_closure_iff.mpr
    intro V hV hyV
    obtain ⟨n, x, hx, hxn⟩ := hh U V hU hV hAU ⟨y, hy, hyV⟩
    exact ⟨f^[n] x, hxn, mem_iUnion.mpr ⟨n, x, hx, rfl⟩⟩

/-- Forward invariance alone suffices in this direction: a forward hitting
orbit is read backwards after swapping its initial and terminal opens. -/
theorem forwardTransitiveOn_symm (T : X ≃ₜ X) (A : Set X) (hTA : MapsTo T A A)
    (ht : forwardTransitiveOn T A) : forwardTransitiveOn T.symm A := by
  apply (forwardTransitiveOn_iff_hitting T.symm A).mpr
  intro U V hU hV hAU hAV
  obtain ⟨n, x, hx, hxn⟩ := (forwardTransitiveOn_iff_hitting T A).mp ht V U hV hU hAV hAU
  refine ⟨n, (T : X → X)^[n] x, ⟨hTA.iterate n hx.1, hxn⟩, ?_⟩
  have hc := T.left_inv.iterate n x
  change (T.symm : X → X)^[n] ((T : X → X)^[n] x) = x at hc
  rw [hc]
  exact hx.2

/-- On a two-sided invariant set, the two transitivity assertions are
equivalent, without compactness or any mixing hypothesis. -/
theorem forwardTransitiveOn_symm_iff (T : X ≃ₜ X) (A : Set X)
    (hTA : MapsTo T A A) (hTiA : MapsTo T.symm A A) :
    forwardTransitiveOn T A ↔ forwardTransitiveOn T.symm A :=
  ⟨forwardTransitiveOn_symm T A hTA,
    fun h => by simpa only [Homeomorph.symm_symm] using forwardTransitiveOn_symm T.symm A hTiA h⟩

/-- The actual isolated core is unchanged when time is reversed. -/
theorem isolatedCore_symm (T : X ≃ₜ X) (K : Set X) :
    isolatedCore T.symm K = isolatedCore T K := by
  simp only [isolatedCore, Homeomorph.symm_symm, inter_comm]

/-- Inverse core transitivity is a consequence of forward core
transitivity and the checked invariance of the actual isolated core. -/
theorem isolatedCore_transitive_symm (T : X ≃ₜ X) (K : Set X)
    (ht : forwardTransitiveOn T (isolatedCore T K)) :
    forwardTransitiveOn T.symm (isolatedCore T.symm K) := by
  rw [isolatedCore_symm]
  exact forwardTransitiveOn_symm T _ (mapsTo_isolatedCore T K) ht

theorem isolatedCore_transitive_symm_iff (T : X ≃ₜ X) (K : Set X) :
    forwardTransitiveOn T (isolatedCore T K) ↔
      forwardTransitiveOn T.symm (isolatedCore T.symm K) :=
  ⟨isolatedCore_transitive_symm T K,
    fun h => by simpa only [Homeomorph.symm_symm] using isolatedCore_transitive_symm T.symm K h⟩

/-- The usual eventual open-set hitting condition of topological mixing
implies the precise transitivity contract consumed by positivity. -/
theorem forwardTransitiveOn_of_eventual_hitting (f : X → X) (A : Set X)
    (hmix : ∀ U V : Set X, IsOpen U → IsOpen V → (A ∩ U).Nonempty → (A ∩ V).Nonempty →
      ∀ᶠ n : ℕ in atTop, ∃ x ∈ A ∩ U, f^[n] x ∈ V) :
    forwardTransitiveOn f A := by
  apply (forwardTransitiveOn_iff_hitting f A).mpr
  intro U V hU hV hAU hAV
  exact (hmix U V hU hV hAU hAV).exists

end LeanShared.ReversibleTransitivity
