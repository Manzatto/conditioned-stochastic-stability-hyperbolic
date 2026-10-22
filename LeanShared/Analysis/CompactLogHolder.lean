module

public import LeanShared.Analysis.RealHolderContinuity
public import LeanShared.Analysis.CompactLocalHolder
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Logarithms of nonvanishing scalar Hölder functions on compact sets
are Hölder with the same exponent. Nonvanishing is required only on the
actual compact set; no globally positive extension is assumed. -/
public noncomputable section
namespace LeanShared.CompactLogHolder
open Set Filter
open scoped Topology ContDiff
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1200000 in
theorem bound {K : Set X} (compact : IsCompact K) (f : X → ℝ) (α C : ℝ)
    (positive : 0 < α) (small : α ≤ 1) (nonnegative : 0 ≤ C)
    (nonzero : ∀ x ∈ K, f x ≠ 0)
    (holder : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ C * dist x y ^ α) :
    ∃ H ≥ 0, ∀ x ∈ K, ∀ y ∈ K, |Real.log (f x) - Real.log (f y)| ≤ H * dist x y ^ α := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp compact
  have continuous : Continuous (fun x : K => f x.val) :=
    (RealHolderContinuity.continuousOn K f α C positive (fun x hx y hy => by
      simpa only [Real.norm_eq_abs] using holder x hx y hy)).domRestrict
  have localBound (x : K) (_ : x ∈ (univ : Set K)) : ∃ U : Set K, IsOpen U ∧ x ∈ U ∧
      ∃ D ≥ 0, ∀ y ∈ U, ∀ z ∈ U,
        dist (Real.log (f y.val)) (Real.log (f z.val)) ≤ D * dist y z ^ α := by
    have smooth : ContDiffAt ℝ 1 Real.log (f x.val) := contDiffAt_id.log (nonzero x x.property)
    obtain ⟨L, W, neighborhood, lipschitz⟩ := smooth.exists_lipschitzOnWith
    have near : (fun y : K => f y.val) ⁻¹' W ∈ nhds x :=
      continuous.continuousAt.preimage_mem_nhds neighborhood
    obtain ⟨U, contained, openU, memberU⟩ := mem_nhds_iff.mp near
    refine ⟨U, openU, memberU, (L : ℝ) * C, mul_nonneg L.coe_nonneg nonnegative, ?_⟩
    intro y hy z hz
    have original : dist (f y.val) (f z.val) ≤ C * dist y z ^ α := by
      simpa only [Real.dist_eq, Subtype.dist_eq] using holder y.val y.property z.val z.property
    exact (lipschitz.dist_le_mul _ (contained hy) _ (contained hz)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left original L.coe_nonneg)
  obtain ⟨H, nonnegativeH, estimate⟩ := CompactLocalHolder.bound_on_compact positive small
    (K := (univ : Set K)) isCompact_univ (fun x : K => Real.log (f x.val)) localBound
  refine ⟨H, nonnegativeH, fun x hx y hy => ?_⟩
  simpa only [Real.dist_eq, Subtype.dist_eq] using estimate ⟨x, hx⟩ (mem_univ _) ⟨y, hy⟩ (mem_univ _)

end LeanShared.CompactLogHolder
