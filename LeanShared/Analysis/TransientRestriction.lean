module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Restriction past a finite transient complement

The complement's nilpotence is an explicit hypothesis. These algebraic
arguments neither identify a geometric exterior with that complement nor
assert that measurable layer projections act on continuous functions.
The scalar may be complex. No finite-dimensionality is needed.
-/

@[expose] public noncomputable section

open Finset

namespace LeanShared.TransientRestriction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The resolvent of a finite transient operator is a finite sum. -/
def finiteResolvent (D : F →L[𝕜] F) (z : 𝕜) (N : ℕ) : F →L[𝕜] F :=
  z⁻¹ • ∑ j ∈ range N, (z⁻¹ • D) ^ j

theorem finiteResolvent_left (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) :
    (z • 1 - D) * finiteResolvent D z N = 1 := by
  let Q := z⁻¹ • D
  have hQ : Q ^ N = 0 := by simp [Q, smul_pow, hD]
  have hfactor : z • (1 - Q) = z • (1 : F →L[𝕜] F) - D := by
    simp [Q, smul_sub, smul_smul, mul_inv_cancel₀ hz]
  rw [← hfactor, finiteResolvent]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz, one_smul]
  change (1 - Q) * ∑ j ∈ range N, Q ^ j = 1
  rw [mul_neg_geom_sum, hQ, sub_zero]

theorem finiteResolvent_right (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) :
    finiteResolvent D z N * (z • 1 - D) = 1 := by
  let Q := z⁻¹ • D
  have hQ : Q ^ N = 0 := by simp [Q, smul_pow, hD]
  have hfactor : z • (1 - Q) = z • (1 : F →L[𝕜] F) - D := by
    simp [Q, smul_sub, smul_smul, mul_inv_cancel₀ hz]
  rw [← hfactor, finiteResolvent]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz, one_smul]
  change (∑ j ∈ range N, Q ^ j) * (1 - Q) = 1
  rw [geom_sum_mul_neg, hQ, sub_zero]

/-- Lower-triangular form: the first coordinate is the retained region. -/
def block (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) :
    (E × F) →L[𝕜] (E × F) :=
  (A.comp (ContinuousLinearMap.fst 𝕜 E F)).prod
    (B.comp (ContinuousLinearMap.fst 𝕜 E F) + D.comp (ContinuousLinearMap.snd 𝕜 E F))

theorem block_apply (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) (u : E) (v : F) :
    block A B D (u, v) = (A u, B u + D v) := rfl

theorem block_mul (A A' : E →L[𝕜] E) (B B' : E →L[𝕜] F) (D D' : F →L[𝕜] F) :
    block A B D * block A' B' D' = block (A * A') (B.comp A' + D.comp B') (D * D') := by
  apply ContinuousLinearMap.ext
  intro x
  rcases x with ⟨u, v⟩
  simp [block_apply, mul_apply_eq_comp, map_add, add_assoc]

/-- The off-diagonal block in the `k`th power. -/
def powerCoupling (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) :
    ℕ → E →L[𝕜] F
  | 0 => 0
  | k + 1 => B.comp (A ^ k) + D.comp (powerCoupling A B D k)

theorem block_pow (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) (k : ℕ) :
    block A B D ^ k = block (A ^ k) (powerCoupling A B D k) (D ^ k) := by
  induction k with
  | zero =>
      apply ContinuousLinearMap.ext
      intro x
      rcases x with ⟨u, v⟩
      simp [powerCoupling, block_apply]
  | succ k ih => rw [pow_succ', ih, block_mul, powerCoupling, pow_succ', pow_succ']

theorem block_sub_scalar (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) (z : 𝕜) :
    block A B D - z • 1 = block (A - z • 1) B (D - z • 1) := by
  apply ContinuousLinearMap.ext
  intro x
  rcases x with ⟨u, v⟩
  simp [block_apply, sub_apply, smul_apply]
  abel

/-- Explicit inverse of the shifted transient complement, with the sign
appropriate to generalized eigenspaces `(D-zI)^k`. -/
def shiftedInverse (D : F →L[𝕜] F) (z : 𝕜) (N : ℕ) : F →L[𝕜] F :=
  -finiteResolvent D z N

theorem shiftedInverse_left (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) :
    shiftedInverse D z N * (D - z • 1) = 1 := by
  have heq : D - z • (1 : F →L[𝕜] F) = -(z • 1 - D) := by abel
  rw [shiftedInverse, heq, neg_mul_neg, finiteResolvent_right D hz N hD]

theorem shiftedInverse_right (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) :
    (D - z • 1) * shiftedInverse D z N = 1 := by
  have heq : D - z • (1 : F →L[𝕜] F) = -(z • 1 - D) := by abel
  rw [shiftedInverse, heq, neg_mul_neg, finiteResolvent_left D hz N hD]

theorem shiftedInverse_pow_left (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) (k : ℕ) :
    shiftedInverse D z N ^ k * (D - z • 1) ^ k = 1 := by
  have hc : Commute (shiftedInverse D z N) (D - z • 1) := by
    rw [Commute, SemiconjBy, shiftedInverse_left D hz N hD, shiftedInverse_right D hz N hD]
  rw [← hc.mul_pow, shiftedInverse_left D hz N hD, one_pow]

theorem shiftedInverse_pow_right (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0)
    (N : ℕ) (hD : D ^ N = 0) (k : ℕ) :
    (D - z • 1) ^ k * shiftedInverse D z N ^ k = 1 := by
  have hc : Commute (D - z • 1) (shiftedInverse D z N) := by
    rw [Commute, SemiconjBy, shiftedInverse_right D hz N hD, shiftedInverse_left D hz N hD]
  rw [← hc.mul_pow, shiftedInverse_right D hz N hD, one_pow]

/-- The ordinary eigenvector lift uses the finite resolvent directly. -/
theorem eigenvector_lift (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (u : E)
    (hu : A u = z • u) :
    block A B D (u, finiteResolvent D z N (B u)) =
      z • (u, finiteResolvent D z N (B u)) := by
  rw [block_apply]
  apply Prod.ext
  · exact hu
  · have hres : z • (finiteResolvent D z N (B u)) -
        D (finiteResolvent D z N (B u)) = B u := by
      change ((z • 1 - D) * finiteResolvent D z N) (B u) = B u
      rw [finiteResolvent_left D hz N hD, one_apply_eq_self]
    change B u + D (finiteResolvent D z N (B u)) = z • (finiteResolvent D z N (B u))
    calc
      B u + D (finiteResolvent D z N (B u)) =
          (z • (finiteResolvent D z N (B u)) - D (finiteResolvent D z N (B u))) +
            D (finiteResolvent D z N (B u)) :=
        congrArg (fun w => w + D (finiteResolvent D z N (B u))) hres.symm
      _ = z • (finiteResolvent D z N (B u)) := sub_add_cancel _ _

/-- An eigenvector on the block is exactly its retained eigenvector and the
unique finite-resolvent lift. -/
theorem eigenvector_iff (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (u : E) (v : F) :
    block A B D (u, v) = z • (u, v) ↔
      A u = z • u ∧ v = finiteResolvent D z N (B u) := by
  constructor
  · intro h
    have hf : A u = z • u := congrArg Prod.fst h
    have hs : B u + D v = z • v := congrArg Prod.snd h
    have heq : z • v - D v = B u := by rw [← hs]; abel
    have hr := congrArg (finiteResolvent D z N) heq
    change (finiteResolvent D z N * (z • 1 - D)) v = finiteResolvent D z N (B u) at hr
    rw [finiteResolvent_right D hz N hD, one_apply_eq_self] at hr
    exact ⟨hf, hr⟩
  · rintro ⟨hf, rfl⟩
    exact eigenvector_lift A B D hz N hD u hf

/-- Restriction to the first coordinate is an equivalence of kernels whenever
the second diagonal block has an explicit two-sided inverse. -/
def kernelRestrictionEquiv (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D R : F →L[𝕜] F) (hDR : D * R = 1) (hRD : R * D = 1) :
    LinearMap.ker (block A B D).toLinearMap ≃ₗ[𝕜] LinearMap.ker A.toLinearMap where
  toFun u := ⟨u.1.1, by
    have hu : block A B D u.1 = 0 := u.2
    have hf := congrArg Prod.fst hu
    exact hf⟩
  invFun u := ⟨(u.1, -(R (B u.1))), by
    change block A B D (u.1, -(R (B u.1))) = 0
    rw [block_apply]
    apply Prod.ext
    · exact u.2
    · change B u.1 + D (-(R (B u.1))) = 0
      rw [map_neg, ← mul_apply_eq_comp, hDR, one_apply_eq_self, add_neg_cancel]⟩
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hu : block A B D u.1 = 0 := u.2
      have hs := congrArg Prod.snd hu
      change B u.1.1 + D u.1.2 = 0 at hs
      have hr := congrArg R hs
      rw [map_add, map_zero, ← mul_apply_eq_comp, hRD, one_apply_eq_self] at hr
      change -(R (B u.1.1)) = u.1.2
      exact (eq_neg_of_add_eq_zero_right hr).symm
  right_inv u := by apply Subtype.ext; rfl
  map_add' u v := by apply Subtype.ext; rfl
  map_smul' a u := by apply Subtype.ext; rfl

/-- The kernel correspondence has bounded restriction and lifting maps. -/
def kernelRestrictionContinuousEquiv (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D R : F →L[𝕜] F) (hDR : D * R = 1) (hRD : R * D = 1) :
    LinearMap.ker (block A B D).toLinearMap ≃L[𝕜] LinearMap.ker A.toLinearMap where
  toLinearEquiv := kernelRestrictionEquiv A B D R hDR hRD
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk
      ((R.continuous.comp (B.continuous.comp continuous_subtype_val)).neg)

/-- The generalized kernel of a continuous operator at a finite Jordan order.
This is Mathlib's natural-order generalized eigenspace, expressed directly
using continuous powers so that the bounded block algebra is visible. -/
def generalizedKernel (T : E →L[𝕜] E) (z : 𝕜) (k : ℕ) : Submodule 𝕜 E :=
  LinearMap.ker (((T - z • 1) ^ k).toLinearMap)

theorem generalizedKernel_eq_genEigenspace (T : E →L[𝕜] E) (z : 𝕜) (k : ℕ) :
    generalizedKernel T z k = Module.End.genEigenspace T.toLinearMap z k := by
  rw [generalizedKernel, Module.End.genEigenspace_nat, ContinuousLinearMap.toLinearMap_pow]
  rfl

/-- Every finite-order generalized eigenvector of the retained operator lifts
uniquely across a nilpotent complement, for each nonzero scalar. -/
def generalizedRestrictionEquiv (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (k : ℕ) :
    generalizedKernel (block A B D) z k ≃ₗ[𝕜] generalizedKernel A z k :=
  LinearEquiv.trans (LinearEquiv.ofEq _ _ (by
      unfold generalizedKernel
      rw [block_sub_scalar, block_pow]))
    (kernelRestrictionEquiv ((A - z • 1) ^ k)
    (powerCoupling (A - z • 1) B (D - z • 1) k) ((D - z • 1) ^ k)
    (shiftedInverse D z N ^ k) (shiftedInverse_pow_right D hz N hD k)
    (shiftedInverse_pow_left D hz N hD k))

theorem generalizedRestrictionEquiv_apply (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (k : ℕ)
    (u : generalizedKernel (block A B D) z k) :
    (generalizedRestrictionEquiv A B D hz N hD k u : E) = u.1.1 := by
  simp only [generalizedRestrictionEquiv]
  change ((LinearEquiv.ofEq _ _ _ u : E × F).1) = u.1.1
  rw [LinearEquiv.coe_ofEq_apply]

/-- The lifting map is the finite inverse of the lower shifted power applied
to its off-diagonal coupling. -/
theorem generalizedRestrictionEquiv_symm_apply (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (k : ℕ)
    (u : generalizedKernel A z k) :
    ((generalizedRestrictionEquiv A B D hz N hD k).symm u : E × F) =
      (u.1, -((shiftedInverse D z N ^ k)
        (powerCoupling (A - z • 1) B (D - z • 1) k u.1))) := by
  simp only [generalizedRestrictionEquiv]
  rfl

/-- Restriction and lifting are bounded maps on every finite generalized
eigenspace; no finite-dimensional norm equivalence is used. -/
def generalizedRestrictionContinuousEquiv (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (k : ℕ) :
    generalizedKernel (block A B D) z k ≃L[𝕜] generalizedKernel A z k :=
  ContinuousLinearEquiv.trans (ContinuousLinearEquiv.ofEq _ _ (by
      unfold generalizedKernel
      rw [block_sub_scalar, block_pow]))
    (kernelRestrictionContinuousEquiv ((A - z • 1) ^ k)
      (powerCoupling (A - z • 1) B (D - z • 1) k) ((D - z • 1) ^ k)
      (shiftedInverse D z N ^ k) (shiftedInverse_pow_right D hz N hD k)
      (shiftedInverse_pow_left D hz N hD k))

/-- In particular, a nonzero generalized eigenvector cannot restrict to zero. -/
theorem generalized_restriction_ne_zero (A : E →L[𝕜] E) (B : E →L[𝕜] F)
    (D : F →L[𝕜] F) {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hD : D ^ N = 0) (k : ℕ)
    (u : E × F) (hu : u ∈ generalizedKernel (block A B D) z k) (hne : u ≠ 0) :
    u.1 ≠ 0 := by
  intro hf
  have hzero : generalizedRestrictionEquiv A B D hz N hD k ⟨u, hu⟩ = 0 := by
    apply Subtype.ext
    rw [generalizedRestrictionEquiv_apply]
    exact hf
  have hzsub : (⟨u, hu⟩ : generalizedKernel (block A B D) z k) = 0 := by
    apply (generalizedRestrictionEquiv A B D hz N hD k).injective
    simpa using hzero
  apply hne
  exact congrArg Subtype.val hzsub

end LeanShared.TransientRestriction
