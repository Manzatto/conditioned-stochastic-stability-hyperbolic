module
public import LeanShared.Analysis.DeterministicCylinderEndpoint
public import LeanShared.Analysis.PressureCoverDomainComparison
public import LeanShared.Analysis.PressureEndpointAsymptotic

/-! The actual reference-word pressure coefficient is controlled by BT's
full open-cylinder coefficient, with just one fixed alphabet factor. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ReferenceCylinderPressure
open PressureCoverRefinement CylinderPrincipalCoefficient
variable {G X J : Type*} [TopologicalSpace G] [TopologicalSpace X]
  [Fintype J] [Nonempty J]

def referenceCost (F : G → X → X) (a : G) (K : Set X) (charts : J → Set X)
    (N : ℕ) (f : X → ℝ) : ℝ :=
  coverCoefficient K (fiber K (FiniteWordCylinders.survivors F K N) (fun _ => a))
    (fun labels => (fun x => ((fun _ : Fin N => a), x)) ⁻¹'
      FiniteWordCylinders.cylinder F charts N labels) f

def fullCost (T : X → X) (K : Set X) (charts : J → Set X) (N : ℕ) (f : X → ℝ) : ℝ :=
  coverCoefficient univ (DeterministicWordCylinders.survivors T K N)
    (DeterministicWordCylinders.cylinder T charts N) f

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem reference_le_full (F : G → X → X) (a : G) (K : Set X) (charts : J → Set X)
    (cover : K ⊆ ⋃ j, charts j) (N : ℕ) (f : X → ℝ)
    (bounded : ∀ i : Fin N → J, BddAbove
      ({0} ∪ f '' ((univ : Set X) ∩ DeterministicWordCylinders.cylinder (F a) charts N i))) :
    referenceCost F a K charts N f ≤ (Fintype.card J : ℝ) * fullCost (F a) K charts N f := by
  have hbK : ∀ i : Fin N → J, BddAbove
      ({0} ∪ f '' (K ∩ DeterministicWordCylinders.cylinder (F a) charts N i)) := by
    intro i
    exact (bounded i).mono (union_subset_union_right _ (image_mono
      (inter_subset_inter_left _ (subset_univ K))))
  have href := DeterministicCylinderEndpoint.coefficient_terminal (F a) K charts cover N f hbK
  have hdomain := PressureCoverDomainComparison.coefficient K univ
    (DeterministicWordCylinders.survivors (F a) K N)
    (DeterministicWordCylinders.cylinder (F a) charts N) f (subset_univ K) bounded
    (DeterministicCylinderEndpoint.cover (F a) K charts cover N)
  have hrefcost : referenceCost F a K charts N f =
      coverCoefficient K (DeterministicWordCylinders.survivors (F a) K (N + 1))
        (DeterministicWordCylinders.cylinder (F a) charts (N + 1)) f := by
    unfold referenceCost
    rw [DeterministicWordCylinders.survivors_fiber]
    congr 1
    funext labels
    exact DeterministicWordCylinders.cylinder_fiber F a charts N labels
  rw [hrefcost]
  exact href.trans (mul_le_mul_of_nonneg_left hdomain (Nat.cast_nonneg _))

end LeanShared.ReferenceCylinderPressure
