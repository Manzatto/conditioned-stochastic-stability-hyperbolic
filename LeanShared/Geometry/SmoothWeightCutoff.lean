module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Algebra.Support

/-! # A constructed smooth cutoff for the actual weight

The cutoff equals one on a prescribed compact retained set and has support
strictly inside its prescribed open collar. Multiplying the actual weight
preserves exact agreement on that retained set. The reference weight's
values away from the basic set are not substituted for the actual weight.
-/

@[expose] public noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace LeanShared.SmoothWeightCutoff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_cutoff (S V : Set M) (hS : IsCompact S) (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ tsupport ζ ⊆ V ∧ (∀ x ∈ S, ζ x = 1) := by
  have hnh : V ∈ 𝓝ˢ S := mem_nhdsSet_iff_exists.mpr ⟨V, hV, hSV, subset_rfl⟩
  obtain ⟨W, hW, hSW, hWV⟩ := hS.exists_isOpen_closure_subset hnh
  obtain ⟨ζ, hsmooth, hbound, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) hW hS.isClosed hSW
  refine ⟨ζ, hsmooth, fun x => hbound (mem_range_self x), ?_, fun x hx => (hone x).mp hx⟩
  change closure (support ζ) ⊆ V
  rw [hsupp]
  exact hWV

/-- The fresh cutoff weight has the actual departure weight on the retained
set, is nonnegative when the weight is, and is supported in the collar. -/
theorem exists_actual_weight_cutoff (S V : Set M) (hS : IsCompact S)
    (hV : IsOpen V) (hSV : S ⊆ V) (w : M → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) :
    ∃ (ζ wc : M → ℝ), ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ ∧
      wc = ζ * w ∧ Continuous wc ∧ (∀ x, 0 ≤ wc x) ∧
      tsupport wc ⊆ V ∧ EqOn wc w S := by
  obtain ⟨ζ, hζ, hζbound, hζsupp, hζone⟩ := exists_cutoff (E := E) S V hS hV hSV
  refine ⟨ζ, ζ * w, hζ, rfl, hζ.continuous.mul hw,
    fun x => mul_nonneg (hζbound x).1 (hw0 x), tsupport_mul_subset_left.trans hζsupp, ?_⟩
  intro x hx
  change ζ x * w x = w x
  rw [hζone x hx, one_mul]

end LeanShared.SmoothWeightCutoff
