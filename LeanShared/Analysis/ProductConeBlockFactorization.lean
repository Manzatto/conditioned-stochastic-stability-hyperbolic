module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! The actual image and preimage cone slopes construct the hyperbolic
block factorization. Both diagonal blocks are derived equivalences, and
the four norm bounds follow from actual component estimates. -/
@[expose] public noncomputable section
open Function
namespace LeanShared.ProductConeBlockFactorization
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def upperLeft (A : (X×Y) →L[ℝ] (X×Y)) : X →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X Y).comp (A.comp (ContinuousLinearMap.inl ℝ X Y))

def upperRight (A : (X×Y) →L[ℝ] (X×Y)) : Y →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X Y).comp (A.comp (ContinuousLinearMap.inr ℝ X Y))

def lowerLeft (A : (X×Y) →L[ℝ] (X×Y)) : X →L[ℝ] Y :=
  (ContinuousLinearMap.snd ℝ X Y).comp (A.comp (ContinuousLinearMap.inl ℝ X Y))

def lowerRight (A : (X×Y) →L[ℝ] (X×Y)) : Y →L[ℝ] Y :=
  (ContinuousLinearMap.snd ℝ X Y).comp (A.comp (ContinuousLinearMap.inr ℝ X Y))

theorem apply_eq (A : (X×Y) →L[ℝ] (X×Y)) (u : X) (s : Y) :
    A (u,s) = (upperLeft A u+upperRight A s, lowerLeft A u+lowerRight A s) := by
  have split : (u,s) = (u,0)+(0,s) := by simp
  rw [split, map_add]
  rfl

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

/-- The graph maps and both diagonal equivalences are constructed from
the actual matrix. No graph factorization or block norm is an input. -/
theorem exists_factorization (A : (X×Y) ≃L[ℝ] (X×Y))
    {c expansionRate contractionRate : ℝ} (nonnegativeC : 0 ≤ c) (positiveexpansionRate : 0 < expansionRate) (nonnegativecontractionRate : 0 ≤ contractionRate)
    (imageSlope : ∀ u : X, ‖(A (u,0)).2‖ ≤ c*‖(A (u,0)).1‖)
    (preimageSlope : ∀ v : X×Y, (A v).1 = 0 → ‖v.1‖ ≤ c*‖v.2‖)
    (expansion : ∀ u : X, expansionRate*‖u‖ ≤ ‖(A (u,0)).1‖)
    (contraction : ∀ v : X×Y, (A v).1 = 0 → ‖(A v).2‖ ≤ contractionRate*‖v.2‖) :
    ∃ J : X ≃L[ℝ] X, ∃ K : Y →L[ℝ] X, ∃ L : X →L[ℝ] Y, ∃ S₀ : Y ≃L[ℝ] Y,
      (∀ u, J u = (A (u,0)).1) ∧
      (∀ s, A (K s,s) = (0,S₀ s)) ∧
      (∀ u s, A (u,s) = (J (u-K s), L (J (u-K s))+S₀ s)) ∧
      ‖K‖ ≤ c ∧ ‖L‖ ≤ c ∧ ‖J.symm.toContinuousLinearMap‖ ≤ expansionRate⁻¹ ∧
        ‖S₀.toContinuousLinearMap‖ ≤ contractionRate := by
  let a := upperLeft A.toContinuousLinearMap
  let b := upperRight A.toContinuousLinearMap
  let d := lowerLeft A.toContinuousLinearMap
  let e := lowerRight A.toContinuousLinearMap
  have zeroKernel (u : X) (zero : a u = 0) : u = 0 := by
    have first : (A (u,0)).1 = 0 := zero
    have second : (A (u,0)).2 = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [first, norm_zero, mul_zero] using imageSlope u) (norm_nonneg _))
    have pairZero : A (u,0) = A (0 : X×Y) := by rw [map_zero]; exact Prod.ext first second
    exact congrArg Prod.fst (A.injective pairZero)
  have injectiveA : Injective a := by
    intro u v equal
    exact sub_eq_zero.mp (zeroKernel (u-v) (by rw [map_sub, equal, sub_self]))
  have surjectiveA : Surjective a := LinearMap.surjective_of_injective (f := a.toLinearMap) injectiveA
  let J : X ≃L[ℝ] X := ContinuousLinearEquiv.ofBijective a
    (LinearMap.ker_eq_bot.mpr injectiveA) (LinearMap.range_eq_top.mpr surjectiveA)
  have coeJ : J.toContinuousLinearMap = a := by
    simp only [J, ContinuousLinearEquiv.coe_ofBijective]
  have Jactual (u : X) : J u = (A (u,0)).1 := by
    change J.toContinuousLinearMap u = a u
    rw [coeJ]
  let K : Y →L[ℝ] X := -(J.symm.toContinuousLinearMap.comp b)
  let L : X →L[ℝ] Y := d.comp J.symm.toContinuousLinearMap
  let s₀ : Y →L[ℝ] Y := e+d.comp K
  have firstZero (s : Y) : (A (K s,s)).1 = 0 := by
    change (A.toContinuousLinearMap (K s,s)).1 = 0
    rw [apply_eq A.toContinuousLinearMap]
    change a (K s)+b s = 0
    rw [← coeJ]
    change J (-(J.symm (b s)))+b s = 0
    rw [map_neg, J.apply_symm_apply, neg_add_cancel]
  have stableGraph (s : Y) : A (K s,s) = (0,s₀ s) := by
    apply Prod.ext
    · exact firstZero s
    · change (A.toContinuousLinearMap (K s,s)).2 = s₀ s
      rw [apply_eq A.toContinuousLinearMap]
      change d (K s)+e s = e s+d (K s)
      exact add_comm _ _
  have zeroStable (s : Y) (zero : s₀ s = 0) : s = 0 := by
    have pairZero : A (K s,s) = A (0 : X×Y) := by
      rw [stableGraph s, zero, map_zero]
      rfl
    exact congrArg Prod.snd (A.injective pairZero)
  have injectiveS : Injective s₀ := by
    intro s t equal
    exact sub_eq_zero.mp (zeroStable (s-t) (by rw [map_sub, equal, sub_self]))
  have surjectiveS : Surjective s₀ := LinearMap.surjective_of_injective (f := s₀.toLinearMap) injectiveS
  let S₀ : Y ≃L[ℝ] Y := ContinuousLinearEquiv.ofBijective s₀
    (LinearMap.ker_eq_bot.mpr injectiveS) (LinearMap.range_eq_top.mpr surjectiveS)
  have coeS : S₀.toContinuousLinearMap = s₀ := by
    simp only [S₀, ContinuousLinearEquiv.coe_ofBijective]
  have stableActual (s : Y) : A (K s,s) = (0,S₀ s) := by
    change A (K s,s) = (0,S₀.toContinuousLinearMap s)
    rw [coeS]
    exact stableGraph s
  have unstableGraph (u : X) : A (u,0) = (J u,L (J u)) := by
    apply Prod.ext
    · exact (Jactual u).symm
    · change d u = d (J.symm (J u))
      rw [J.symm_apply_apply]
  refine ⟨J, K, L, S₀, Jactual, stableActual, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s
    have split : (u,s) = (u-K s,0)+(K s,s) := by ext <;> simp
    rw [split, map_add, unstableGraph, stableActual]
    simp only [Prod.mk_add_mk, add_zero]
  · apply ContinuousLinearMap.opNorm_le_bound _ nonnegativeC
    intro s
    exact preimageSlope (K s,s) (firstZero s)
  · apply ContinuousLinearMap.opNorm_le_bound _ nonnegativeC
    intro u
    have slope := imageSlope (J.symm u)
    rw [← Jactual, J.apply_symm_apply] at slope
    exact slope
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr positiveexpansionRate.le)
    intro u
    have lower := expansion (J.symm u)
    rw [← Jactual, J.apply_symm_apply] at lower
    have divide : ‖J.symm u‖ ≤ ‖u‖/expansionRate := (le_div_iff₀ positiveexpansionRate).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm, ContinuousLinearEquiv.coe_coe] using divide
  · apply ContinuousLinearMap.opNorm_le_bound _ nonnegativecontractionRate
    intro s
    have bound := contraction (K s,s) (firstZero s)
    rw [stableActual] at bound
    exact bound

end LeanShared.ProductConeBlockFactorization
