module
public import LeanShared.Geometry.ManifoldSmoothHolderCore
public import LeanShared.Geometry.ManifoldHolderQuotientMultiplier
public import LeanShared.Geometry.SupportedCorePhysicalRealization

/-! Bounds on the constructed lower-regularity manifold core: the supremum of a
smooth supported function on any subset is at most a fixed multiple of its
lower-regularity norm, and multiplication by a smooth global function is bounded
on the smooth core. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldSmoothHolderCore
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (region : V ⊆ S)

local instance lowerNormed' : NormedAddCommGroup (Lower e D openV hb hb1) := inferInstance
local instance lowerSeminormed' : SeminormedAddCommGroup (Lower e D openV hb hb1) :=
  (lowerNormed' e D openV hb hb1).toSeminormedAddCommGroup

include region in
/-- The supremum on `K` is controlled by the lower-regularity norm. -/
theorem uniform_bound (K : Set M) [CompactSpace K] (c : SmoothSupportedManifoldCore.core (E := E) V) :
    ‖SmoothSupportedManifoldCore.physicalCore V K c‖ ≤
      ‖physical e D openV hb hb1‖ * ‖smooth e D atlas openV hb hb1 c‖ := by
  refine ((BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_)
  have h := (physical e D openV hb hb1 (smooth e D atlas openV hb hb1 c)).norm_coe_le_norm x.val
  rw [physical_smooth e D atlas openV hb hb1 region c x.val] at h
  change ‖c.val x.val‖ ≤ _
  exact h.trans ((physical e D openV hb hb1).le_opNorm _)

include region in
/-- Multiplication by a smooth global function is bounded on the smooth core. -/
theorem smooth_multiplier_bound (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ) :
    ∃ B : ℝ, ∀ c : SmoothSupportedManifoldCore.core (E := E) V,
      ‖smooth e D atlas openV hb hb1 (SmoothSupportedManifoldCore.multiplier V ψ hψ c)‖ ≤
        B * ‖smooth e D atlas openV hb hb1 c‖ := by
  obtain ⟨B, -, bound⟩ := ManifoldHolderQuotient.multiplier_bound (regions e D openV) hb hb1
    (fun i => atlas i) ψ hψ
  refine ⟨B, fun c => ?_⟩
  obtain ⟨w, hw, hnorm⟩ := bound (smooth e D atlas openV hb hb1 c)
  have same : smooth e D atlas openV hb hb1 (SmoothSupportedManifoldCore.multiplier V ψ hψ c) = w := by
    apply physical_injective e D openV hb hb1
    ext x
    rw [physical_smooth e D atlas openV hb hb1 region]
    change _ = ManifoldHolderQuotient.physical (regions e D openV) hb hb1 w x
    rw [hw]
    change c.val x * ψ x = ψ x * physical e D openV hb hb1 (smooth e D atlas openV hb hb1 c) x
    rw [physical_smooth e D atlas openV hb hb1 region, mul_comm]
  rw [same]
  exact hnorm

end LeanShared.ManifoldSmoothHolderCore
