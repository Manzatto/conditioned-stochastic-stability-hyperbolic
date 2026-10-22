module
public import LeanShared.Analysis.DomainPressureRefinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Adding a terminal chart to a cylinder cover costs only the cardinality
of the fixed alphabet. This isolates the N+1 versus N indexing issue in
matching the actual chronological cylinders to BT (2008), (3.2). -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.PressureCoverFiniteRefinement
open PressureCoverRefinement DomainPressureRefinement
variable {X I J : Type*} [TopologicalSpace X] [Fintype J] [Nonempty J]

omit [TopologicalSpace X] in
private theorem cost_bddBelow (K : Set X) (u : I → Set X) (f : X → ℝ)
    (hb : ∀ i, BddAbove ({0} ∪ f '' (K ∩ u i))) (S : Set X) :
    BddBelow {a : ℝ | ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
      a = ∑ i ∈ c, domainCoefficient K (u i) f} := by
  refine ⟨0, ?_⟩
  rintro a ⟨c, hc, rfl⟩
  exact Finset.sum_nonneg fun i _ => domainCoefficient_nonneg_of_bdd (hb i)

omit [TopologicalSpace X] in
/-- A finite additional endpoint observation has no exponential cost. -/
theorem refine (K S S' : Set X) (u : I → Set X) (v : J → Set X) (f : X → ℝ)
    (hb : ∀ i, BddAbove ({0} ∪ f '' (K ∩ u i)))
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i)
    (hS : S' ⊆ S) (hv : S' ⊆ ⋃ j, v j) :
    coverCoefficient K S' (fun ij : I × J => u ij.1 ∩ v ij.2) f ≤
      (Fintype.card J : ℝ) * coverCoefficient K S u f := by
  classical
  have hb' : ∀ ij : I × J, BddAbove ({0} ∪ f '' (K ∩ (u ij.1 ∩ v ij.2))) := by
    intro ij
    exact (hb ij.1).mono (union_subset_union_right _ (image_mono (by tauto_set)))
  have hbound : ∀ c : Finset I, S ⊆ ⋃ i ∈ c, u i →
      coverCoefficient K S' (fun ij : I × J => u ij.1 ∩ v ij.2) f ≤
        (Fintype.card J : ℝ) * ∑ i ∈ c, domainCoefficient K (u i) f := by
    intro c hc
    have hcov : S' ⊆ ⋃ ij ∈ c ×ˢ (Finset.univ : Finset J), u ij.1 ∩ v ij.2 := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hc (hS hx))
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hv hx)
      exact mem_iUnion₂.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, hxi, hxj⟩
    apply (csInf_le (cost_bddBelow K _ f hb' S') ⟨_, hcov, rfl⟩).trans
    calc
      (∑ ij ∈ c ×ˢ (Finset.univ : Finset J), domainCoefficient K (u ij.1 ∩ v ij.2) f) ≤
          ∑ ij ∈ c ×ˢ (Finset.univ : Finset J), domainCoefficient K (u ij.1) f := by
        apply Finset.sum_le_sum
        intro ij hij
        exact domainCoefficient_mono_of_bdd (hb ij.1) inter_subset_left
      _ = (Fintype.card J : ℝ) * ∑ i ∈ c, domainCoefficient K (u i) f := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.mul_sum]
  have hcard : (0 : ℝ) < Fintype.card J := Nat.cast_pos.mpr Fintype.card_pos
  have hsne : {a : ℝ | ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
      a = ∑ i ∈ c, domainCoefficient K (u i) f}.Nonempty := by
    obtain ⟨c, hc⟩ := hcover
    exact ⟨_, c, hc, rfl⟩
  have hdiv : coverCoefficient K S' (fun ij : I × J => u ij.1 ∩ v ij.2) f /
      (Fintype.card J : ℝ) ≤ coverCoefficient K S u f := by
    apply le_csInf hsne
    rintro a ⟨c, hc, rfl⟩
    exact (div_le_iff₀ hcard).mpr (by simpa only [mul_comm] using hbound c hc)
  exact (by simpa only [mul_comm] using (div_le_iff₀ hcard).mp hdiv)

end LeanShared.PressureCoverFiniteRefinement
