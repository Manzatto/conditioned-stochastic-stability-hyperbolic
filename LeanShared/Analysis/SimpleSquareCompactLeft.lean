module

public import LeanShared.Analysis.SquareCompactFredholm
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-! A normalized left eigenfunctional for an algebraically simple nonzero
eigenvalue of a square-compact operator. A finite-rank perturbation and the
proved Fredholm alternative replace contour/Riesz-projector assumptions. -/

public noncomputable section
open Module ContinuousLinearMap

namespace LeanShared.SimpleSquareCompactLeft

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] [LocallyCompactSpace 𝕜]

omit [CompleteSpace X] in
/-- Adding a rank-one map preserves compactness of the square. -/
theorem square_compact_add_rankOne (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    (φ : X →L[𝕜] 𝕜) (v : X) :
    IsCompactOperator ((T + φ.smulRight v) ^ 2 : X →L[𝕜] X) := by
  let p := φ.smulRight v
  have hp : IsCompactOperator p :=
    (isCompactOperator_of_locallyCompactSpace_dom φ).continuous_comp
      (continuous_id.smul continuous_const)
  have he : (T + p) ^ 2 = T ^ 2 + (T * p + p * T + p * p) := by noncomm_ring
  rw [he]
  exact hT.add (((hp.continuous_comp T.continuous).add
    (hp.comp_clm T)).add (hp.comp_clm p))

/-- Algebraic simplicity through order two suffices to construct a normalized
bounded left functional. No left eigenvector, projection or spectral gap is assumed. -/
theorem exists_left (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    (μ : 𝕜) (hμ : μ ≠ 0) (v : X) (hv : v ≠ 0) (heig : T v = μ • v)
    (simple : ∀ x : X, ((T - μ • 1 : X →L[𝕜] X) ^ 2) x = 0 → ∃ a : 𝕜, x = a • v) :
    ∃ ℓ : X →L[𝕜] 𝕜, ℓ v = 1 ∧ ∀ x, ℓ (T x) = μ * ℓ x := by
  obtain ⟨φ₀, _, hφ₀⟩ := exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)
  let φ := (φ₀ v)⁻¹ • φ₀
  have hφ₀ne : φ₀ v ≠ 0 := by rw [hφ₀]; exact_mod_cast norm_ne_zero_iff.mpr hv
  have hφ : φ v = 1 := by simp [φ, hφ₀ne]
  let p := φ.smulRight v
  let S := T - μ • 1
  have hSv : S v = 0 := by simp [S, heig]
  have hinj : Function.Injective (T + p - μ • 1 : X →L[𝕜] X) := by
    apply (T + p - μ • 1).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hSx : S x = -(φ x) • v := by
      change T x + φ x • v - μ • x = 0 at hx
      change T x - μ • x = _
      linear_combination (norm := module) hx
    have hSS : (S ^ 2) x = 0 := by
      rw [pow_two, mul_apply_eq_comp, hSx, map_smul, hSv, smul_zero]
    obtain ⟨a, rfl⟩ := simple x hSS
    have ha : a = 0 := by
      have hh : a • v = 0 := by simpa [p, heig, hφ, map_smul, smul_smul] using hx
      exact (smul_eq_zero.mp hh).resolve_right hv
    simp [ha]
  have surj := SquareCompactFredholm.surjective_shift (T + p)
    (square_compact_add_rankOne T hT φ v) hμ hinj
  let e : X ≃L[𝕜] X := ContinuousLinearEquiv.ofBijective (T + p - μ • 1)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr surj)
  have hev : e v = v := by change T v + φ v • v - μ • v = v; rw [heig, hφ, one_smul]; abel
  have heinv : e.symm v = v := by apply e.injective; rw [e.apply_symm_apply, hev]
  let ℓ := φ.comp e.symm.toContinuousLinearMap
  have hℓv : ℓ v = 1 := by change φ (e.symm v) = 1; rw [heinv, hφ]
  refine ⟨ℓ, hℓv, fun x => ?_⟩
  have hh : ℓ (e x) = φ x := by change φ (e.symm (e x)) = φ x; rw [e.symm_apply_apply]
  change ℓ (T x + φ x • v - μ • x) = φ x at hh
  simp only [map_sub, map_add, map_smul, hℓv, smul_eq_mul, mul_one] at hh
  linear_combination hh

end LeanShared.SimpleSquareCompactLeft
