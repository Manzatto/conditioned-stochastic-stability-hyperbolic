module
public import LeanShared.Dynamics.DeterministicWordCylinders
public import LeanShared.Analysis.PressureCoverFiniteRefinement
public import LeanShared.Analysis.PressureCoverReindex

/-! The literal N+1-observation pressure coefficient is at most the
N-letter BT coefficient times the fixed chart alphabet size. The density
at horizon N is identical on both sides; no shift of the potential occurs. -/
@[expose] public noncomputable section
open Set Function
open scoped BigOperators
namespace LeanShared.DeterministicCylinderEndpoint
open DeterministicWordCylinders PressureCoverRefinement
variable {X J : Type*} [TopologicalSpace X] [Fintype J] [Nonempty J]

omit [TopologicalSpace X] [Nonempty J] in
theorem cover (T : X → X) (K : Set X) (charts : J → Set X)
    (hcover : K ⊆ ⋃ j, charts j) (N : ℕ) :
    ∃ c : Finset (Fin N → J), survivors T K N ⊆ ⋃ i ∈ c, cylinder T charts N i := by
  classical
  refine ⟨Finset.univ, ?_⟩
  intro x hx
  have hlabels : ∀ n : Fin N, ∃ j, T^[n.val] x ∈ charts j :=
    fun n => mem_iUnion.mp (hcover (hx n))
  choose labels hlabels using hlabels
  exact mem_iUnion₂.mpr ⟨labels, Finset.mem_univ _, hlabels⟩

omit [TopologicalSpace X] in
theorem coefficient_terminal (T : X → X) (K : Set X) (charts : J → Set X)
    (hcover : K ⊆ ⋃ j, charts j) (N : ℕ) (f : X → ℝ)
    (hb : ∀ i : Fin N → J, BddAbove ({0} ∪ f '' (K ∩ cylinder T charts N i))) :
    coverCoefficient K (survivors T K (N + 1)) (cylinder T charts (N + 1)) f ≤
      (Fintype.card J : ℝ) * coverCoefficient K (survivors T K N) (cylinder T charts N) f := by
  let e : ((Fin N → J) × J) ≃ (Fin (N + 1) → J) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (N + 1) => J))
  have hsets : (fun ij : (Fin N → J) × J => cylinder T charts (N + 1) (e ij)) =
      (fun ij => cylinder T charts N ij.1 ∩ (T^[N]) ⁻¹' charts ij.2) := by
    funext ij
    exact cylinder_snoc T charts N ij.1 ij.2
  have hreindex := PressureCoverReindex.coefficient e K (survivors T K (N + 1))
    (cylinder T charts (N + 1)) f
  rw [hsets] at hreindex
  rw [← hreindex]
  apply PressureCoverFiniteRefinement.refine K (survivors T K N) (survivors T K (N + 1))
    (cylinder T charts N) (fun j => (T^[N]) ⁻¹' charts j) f hb (cover T K charts hcover N)
  · intro x hx j
    exact hx j.castSucc
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (hx (Fin.last N)))
    refine mem_iUnion.mpr ⟨j, ?_⟩
    simpa only [Fin.val_last, mem_preimage] using hj

end LeanShared.DeterministicCylinderEndpoint
