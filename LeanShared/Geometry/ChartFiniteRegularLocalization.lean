module
public import LeanShared.Geometry.ChartLocalization

/-! Integer-order chart localization of actual finitely differentiable
functions. Only the cutoff and atlas are smooth; the input is not
silently upgraded to C∞. Compact cutoff support proves smoothness of
zero extension up to the given finite order. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ChartLocalization
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (θ : M → ℂ)
  (support : tsupport θ ⊆ e.source)
  (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (hθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compact : HasCompactSupport θ)

include support he hθ compact in
theorem coordinate_contDiff_of_order {n : ℕ∞} {f : M → ℂ}
    (hf : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) n f) :
    ContDiff ℝ n (coordinate e θ f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · have inverse : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) n e.symm y :=
      (contMDiffAt_symm_of_mem_maximalAtlas he hy).of_le (by simp)
    have localized : ContDiffAt ℝ n (fun z => θ (e.symm z) * f (e.symm z)) y :=
      (((hθ (e.symm y)).of_le (by simp)).comp y inverse).contDiffAt.mul
        (((hf (e.symm y)).comp y inverse).contDiffAt)
    apply localized.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact ite_eq_left hz
  · have outside : y ∉ localSupport e θ :=
      fun hn => hy (localSupport_subset_target e θ support hn)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(localSupport_isCompact e θ support compact).isClosed.isOpen_compl.mem_nhds outside]
      with z hz
    exact coordinate_zero_outside e θ f z hz
end LeanShared.ChartLocalization
