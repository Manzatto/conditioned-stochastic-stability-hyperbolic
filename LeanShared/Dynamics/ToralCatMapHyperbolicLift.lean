module

public import LeanShared.Dynamics.ToralCatMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Explicit uniform hyperbolicity of the real lift of the concrete toral
cat map. The stable and unstable lines are complementary and have rank
one; every forward stable and backward unstable iterate has exactly the
contracting norm factor. This is linear geometry on the actual lift, not
an assumed tangent-bundle or full-HL certificate on its torus quotient. -/

public noncomputable section
namespace LeanShared.ToralCatMap
open Set Function
open scoped ContDiff

@[expose] def contracting : ℝ := (3 - Real.sqrt 5) / 2
@[expose] def expanding : ℝ := (3 + Real.sqrt 5) / 2

theorem sqrt_five_bounds : 1 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have nonnegative := Real.sqrt_nonneg (5 : ℝ)
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  constructor <;> nlinarith

theorem contracting_pos : 0 < contracting := by
  have := sqrt_five_bounds.2
  unfold contracting
  linarith

theorem contracting_lt_one : contracting < 1 := by
  have := sqrt_five_bounds.1
  unfold contracting
  linarith

theorem expanding_gt_one : 1 < expanding := by
  have := sqrt_five_bounds.1
  unfold expanding
  linarith

theorem eigenvalue_sum : contracting + expanding = 3 := by
  unfold contracting expanding
  ring

theorem eigenvalue_product : contracting * expanding = 1 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold contracting expanding
  nlinarith

theorem contracting_quadratic : contracting ^ 2 - 3 * contracting + 1 = 0 := by
  nlinarith [eigenvalue_sum, eigenvalue_product]

theorem expanding_quadratic : expanding ^ 2 - 3 * expanding + 1 = 0 := by
  nlinarith [eigenvalue_sum, eigenvalue_product]

theorem eigenvalues_distinct : expanding - contracting ≠ 0 := by
  have := expanding_gt_one
  have := contracting_lt_one
  linarith

@[expose] def stableVector : ℝ × ℝ := (contracting - 1, 1)
@[expose] def unstableVector : ℝ × ℝ := (expanding - 1, 1)
@[expose] def stable : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {stableVector}
@[expose] def unstable : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {unstableVector}

@[expose] def linear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := map
  map_add' := by intro x y; ext <;> simp [map] <;> ring
  map_smul' := by
    intro a x
    ext <;> simp [map, Prod.smul_mk, smul_eq_mul] <;> ring

@[expose] def inverseLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := inverse
  map_add' := by intro x y; ext <;> simp [inverse] <;> ring
  map_smul' := by
    intro a x
    ext <;> simp [inverse, Prod.smul_mk, smul_eq_mul] <;> ring

theorem contDiff_map : ContDiff ℝ ∞ (map (G := ℝ)) := by
  simpa [LinearMap.coe_toContinuousLinearMap', linear] using
    (linear.toContinuousLinearMap.contDiff : ContDiff ℝ ∞ linear.toContinuousLinearMap)

theorem contDiff_inverse : ContDiff ℝ ∞ (inverse (G := ℝ)) := by
  simpa [LinearMap.coe_toContinuousLinearMap', inverseLinear] using
    (inverseLinear.toContinuousLinearMap.contDiff : ContDiff ℝ ∞ inverseLinear.toContinuousLinearMap)

theorem fderiv_map (x : ℝ × ℝ) : fderiv ℝ (map (G := ℝ)) x = linear.toContinuousLinearMap := by
  have derivative : HasFDerivAt (map (G := ℝ)) linear.toContinuousLinearMap x := by
    simpa [LinearMap.coe_toContinuousLinearMap', linear] using
      linear.toContinuousLinearMap.hasFDerivAt (x := x)
  exact derivative.fderiv

theorem fderiv_inverse (x : ℝ × ℝ) :
    fderiv ℝ (inverse (G := ℝ)) x = inverseLinear.toContinuousLinearMap := by
  have derivative : HasFDerivAt (inverse (G := ℝ)) inverseLinear.toContinuousLinearMap x := by
    simpa [LinearMap.coe_toContinuousLinearMap', inverseLinear] using
      inverseLinear.toContinuousLinearMap.hasFDerivAt (x := x)
  exact derivative.fderiv

theorem map_stableVector : map stableVector = contracting • stableVector := by
  ext <;> simp only [map, stableVector, Prod.smul_mk, smul_eq_mul] <;>
    nlinarith [contracting_quadratic]

theorem map_unstableVector : map unstableVector = expanding • unstableVector := by
  ext <;> simp only [map, unstableVector, Prod.smul_mk, smul_eq_mul] <;>
    nlinarith [expanding_quadratic]

theorem inverse_unstableVector : inverse unstableVector = contracting • unstableVector := by
  ext <;> simp only [inverse, unstableVector, Prod.smul_mk, smul_eq_mul] <;>
    nlinarith [eigenvalue_sum, eigenvalue_product]

/-- The exact stable and unstable eigenspaces span the entire real lift. -/
theorem stable_unstable_isCompl : IsCompl stable unstable := by
  have disjoint : Disjoint stable unstable := by
    rw [Submodule.disjoint_def]
    intro v stableV unstableV
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp stableV
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp unstableV
    have first := congrArg Prod.fst (ha.trans hb.symm)
    have second := congrArg Prod.snd (ha.trans hb.symm)
    simp only [stableVector, unstableVector, Prod.smul_mk, smul_eq_mul, mul_one] at first second
    rw [← second] at first
    have zeroA : a = 0 := by
      have product : a * (expanding - contracting) = 0 := by nlinarith
      exact (mul_eq_zero.mp product).resolve_right eigenvalues_distinct
    rw [← ha, zeroA, zero_smul]
  have spanning : stable ⊔ unstable = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro v
    let a := ((expanding - 1) * v.2 - v.1) / (expanding - contracting)
    let b := (v.1 - (contracting - 1) * v.2) / (expanding - contracting)
    apply Submodule.mem_sup.mpr
    refine ⟨a • stableVector, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩,
      b • unstableVector, Submodule.mem_span_singleton.mpr ⟨b, rfl⟩, ?_⟩
    ext <;> simp [stableVector, unstableVector, Prod.smul_mk, smul_eq_mul, a, b] <;>
      field_simp [eigenvalues_distinct] <;> ring
  exact ⟨disjoint, codisjoint_iff.mpr spanning⟩

theorem stable_finrank : Module.finrank ℝ stable = 1 := by
  apply finrank_span_singleton
  intro zero
  have := congrArg Prod.snd zero
  norm_num [stableVector] at this

theorem unstable_finrank : Module.finrank ℝ unstable = 1 := by
  apply finrank_span_singleton
  intro zero
  have := congrArg Prod.snd zero
  norm_num [unstableVector] at this

/-- The constructed continuous splitting projection has exactly the
stable range and unstable kernel required by hyperbolic tangent data. -/
@[expose] def projection : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap (stable.projection unstable stable_unstable_isCompl)

theorem projection_range : projection.toLinearMap.range = stable := by
  simp only [projection, LinearMap.coe_toContinuousLinearMap, Submodule.range_projection]

theorem projection_kernel : projection.toLinearMap.ker = unstable := by
  simp only [projection, LinearMap.coe_toContinuousLinearMap, Submodule.ker_projection]

theorem projection_idempotent : projection.comp projection = projection := by
  apply ContinuousLinearMap.ext
  intro v
  change stable.projection unstable stable_unstable_isCompl
    (stable.projection unstable stable_unstable_isCompl v) =
      stable.projection unstable stable_unstable_isCompl v
  simpa only [Module.End.mul_apply] using congrArg
    (fun f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) => f v)
    (Submodule.isIdempotentElem_projection stable_unstable_isCompl).eq

theorem map_stable (v : ℝ × ℝ) (member : v ∈ stable) : map v = contracting • v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp member
  change linear (a • stableVector) = contracting • (a • stableVector)
  rw [linear.map_smul]
  change a • map stableVector = contracting • (a • stableVector)
  rw [map_stableVector, smul_comm]

theorem inverse_unstable (v : ℝ × ℝ) (member : v ∈ unstable) : inverse v = contracting • v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp member
  change inverseLinear (a • unstableVector) = contracting • (a • unstableVector)
  rw [inverseLinear.map_smul]
  change a • inverse unstableVector = contracting • (a • unstableVector)
  rw [inverse_unstableVector, smul_comm]

theorem map_unstable (v : ℝ × ℝ) (member : v ∈ unstable) : map v = expanding • v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp member
  change linear (a • unstableVector) = expanding • (a • unstableVector)
  rw [linear.map_smul]
  change a • map unstableVector = expanding • (a • unstableVector)
  rw [map_unstableVector, smul_comm]

private theorem map_submodule_of_scalar
    (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (S : Submodule ℝ (ℝ × ℝ))
    (c : ℝ) (nonzero : c ≠ 0) (eigen : ∀ v ∈ S, L v = c • v) : S.map L = S := by
  ext v
  constructor
  · rintro ⟨w, member, rfl⟩
    rw [eigen w member]
    exact S.smul_mem c member
  · intro member
    refine ⟨c⁻¹ • v, S.smul_mem _ member, ?_⟩
    rw [L.map_smul, eigen v member, smul_smul, inv_mul_cancel₀ nonzero, one_smul]

theorem stable_invariant : stable.map linear = stable :=
  map_submodule_of_scalar linear stable contracting contracting_pos.ne' map_stable

theorem unstable_invariant : unstable.map linear = unstable :=
  map_submodule_of_scalar linear unstable expanding (zero_lt_one.trans expanding_gt_one).ne' map_unstable

theorem iterate_stable (n : ℕ) (v : ℝ × ℝ) (member : v ∈ stable) :
    (map (G := ℝ))^[n] v = contracting ^ n • v := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
  | succ n induction =>
    rw [Function.iterate_succ_apply', induction]
    change linear (contracting ^ n • v) = contracting ^ (n + 1) • v
    rw [linear.map_smul]
    change contracting ^ n • map v = contracting ^ (n + 1) • v
    rw [map_stable v member, smul_smul, pow_succ]

theorem inverse_iterate_unstable (n : ℕ) (v : ℝ × ℝ) (member : v ∈ unstable) :
    (inverse (G := ℝ))^[n] v = contracting ^ n • v := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
  | succ n induction =>
    rw [Function.iterate_succ_apply', induction]
    change inverseLinear (contracting ^ n • v) = contracting ^ (n + 1) • v
    rw [inverseLinear.map_smul]
    change contracting ^ n • inverse v = contracting ^ (n + 1) • v
    rw [inverse_unstable v member, smul_smul, pow_succ]

theorem norm_iterate_stable (n : ℕ) (v : ℝ × ℝ) (member : v ∈ stable) :
    ‖(map (G := ℝ))^[n] v‖ = contracting ^ n * ‖v‖ := by
  rw [iterate_stable n v member, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg contracting_pos.le n)]

theorem norm_inverse_iterate_unstable (n : ℕ) (v : ℝ × ℝ) (member : v ∈ unstable) :
    ‖(inverse (G := ℝ))^[n] v‖ = contracting ^ n * ‖v‖ := by
  rw [inverse_iterate_unstable n v member, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg contracting_pos.le n)]

end LeanShared.ToralCatMap
