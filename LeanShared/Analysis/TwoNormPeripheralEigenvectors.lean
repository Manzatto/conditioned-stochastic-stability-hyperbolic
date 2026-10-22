module

public import LeanShared.Analysis.CompactTwoNormFredholm
public import LeanShared.Analysis.CompactTwoNormEigenSpace
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Compactness in the weaker norm turns every spectral value above the
strong growth cutoff into an actual eigenvalue. A lower bound on the whole
spectral radius then constructs a peripheral eigenvector. No sign, simplicity,
or exclusion of other peripheral spectral values is asserted. -/

public noncomputable section

namespace LeanShared.CompactTwoNormFredholm
open ContinuousLinearMap
open Filter Topology
open scoped ENNReal

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A compact operator that controls the original norm forces finite
dimension. This is the compactness argument needed on a peripheral eigenspace. -/
theorem finiteDimensional_of_compact_lower_bound
    (i : X →L[ℂ] W) (hi : IsCompactOperator i) (A : ℝ) (hA : 0 ≤ A)
    (lower : ∀ x, ‖x‖ ≤ A * ‖i x‖) : FiniteDimensional ℂ X :=
  CompactTwoNormEigenSpace.finiteDimensional_of_compact_bound i hi A hA lower

/-- A single strong contraction estimate makes every eigenspace beyond its
cutoff finite-dimensional. This does not assert dimension one. -/
theorem finiteDimensional_eigenspace_of_power_estimate
    (T : X →L[ℂ] X) (i : X →L[ℂ] W) (hi : IsCompactOperator i)
    (z : ℂ) (n : ℕ) (θ D : ℝ) (hD : 0 ≤ D) (gap : θ < ‖z ^ n‖)
    (estimate : ∀ x, ‖(T ^ n) x‖ ≤ θ * ‖x‖ + D * ‖i x‖) :
    FiniteDimensional ℂ (Module.End.eigenspace (T : Module.End ℂ X) z) := by
  let S := Module.End.eigenspace (T : Module.End ℂ X) z
  let j : S →L[ℂ] W := i.comp S.subtypeL
  have compactJ : IsCompactOperator j := hi.comp_clm S.subtypeL
  have positive : 0 < ‖z ^ n‖ - θ := sub_pos.mpr gap
  apply finiteDimensional_of_compact_lower_bound j compactJ
    (D / (‖z ^ n‖ - θ)) (div_nonneg hD positive.le)
  intro x
  have eigen : T x.val = z • x.val := Module.End.mem_eigenspace_iff.mp x.property
  have iterate (k : ℕ) : (T ^ k) x.val = z ^ k • x.val := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, eigen, smul_smul]
      rw [pow_succ]
  have bound := estimate x.val
  rw [iterate, norm_smul] at bound
  change ‖x.val‖ ≤ D / (‖z ^ n‖ - θ) * ‖i x.val‖
  rw [div_mul_eq_mul_div, le_div_iff₀ positive]
  nlinarith

/-- Compact two-norm control gives finite-dimensional eigenspaces throughout
the region in which the Fredholm alternative applies. -/
theorem finiteDimensional_eigenspace
    (T : X →L[ℂ] X) (i : X →L[ℂ] W) (hi : IsCompactOperator i)
    (α R C D : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    FiniteDimensional ℂ (Module.End.eigenspace (T : Module.End ℂ X) z) := by
  have positive : 0 < ‖z‖ := hα.trans_lt hz
  have ratio : α / ‖z‖ < 1 := (div_lt_one positive).mpr hz
  have tends : Tendsto (fun n : ℕ => C * (α / ‖z‖) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα positive.le) ratio).const_mul C
  obtain ⟨n, small⟩ := (tends.eventually (gt_mem_nhds zero_lt_one)).exists
  have gap : C * α ^ n < ‖z ^ n‖ := by
    rw [norm_pow]
    rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos positive n)] at small
    exact small
  exact finiteDimensional_eigenspace_of_power_estimate T i hi z n
    (C * α ^ n) (D * R ^ n) (mul_nonneg hD (pow_nonneg hR n)) gap (estimate n)

/-- The proved compact two-norm Fredholm alternative excludes residual
spectrum outside the strong growth disk. -/
theorem eigenvector_of_mem_spectrum (T : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) (spectral : z ∈ spectrum ℂ T) :
    ∃ x : X, x ≠ 0 ∧ T x = z • x := by
  by_contra! absent
  have injective : Function.Injective (T - z • 1 : X →L[ℂ] X) := by
    intro x y equal
    have zero : (T - z • 1) (x - y) = 0 := by
      rw [map_sub, equal, sub_self]
    have eigen : T (x - y) = z • (x - y) := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using zero
    exact sub_eq_zero.mp (by_contra (fun nonzero => absent (x - y) nonzero eigen))
  have surjective := surjective_of_twoNorm T i hi α R C D hα hR hC hD estimate
    z hz injective
  have unit : IsUnit (T - z • 1 : X →L[ℂ] X) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨injective, surjective⟩
  apply spectral
  rw [spectrum.mem_resolventSet_iff]
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using unit.neg

/-- A whole-radius lower bound strictly above the strong cutoff produces
an actual peripheral eigenvector, even when no leading eigenvalue has yet
been identified with that positive real lower bound. -/
theorem exists_peripheral_eigenvector [Nontrivial X]
    (T : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (r : ℝ) (cutoff : α < r) (lower : ENNReal.ofReal r ≤ spectralRadius ℂ T) :
    ∃ z : ℂ, ∃ x : X, x ≠ 0 ∧ T x = z • x ∧
      ENNReal.ofReal ‖z‖ = spectralRadius ℂ T ∧ r ≤ ‖z‖ := by
  obtain ⟨z, spectral, norm_eq⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty T)
  have norm_eq' : ENNReal.ofReal ‖z‖ = spectralRadius ℂ T := by
    simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm] using norm_eq
  have large : r ≤ ‖z‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg z)).mp
    exact lower.trans_eq norm_eq'.symm
  obtain ⟨x, nonzero, eigen⟩ := eigenvector_of_mem_spectrum T i hi α R C D
    hα hR hC hD estimate z (cutoff.trans_le large) spectral
  exact ⟨z, x, nonzero, eigen, norm_eq', large⟩

end LeanShared.CompactTwoNormFredholm
