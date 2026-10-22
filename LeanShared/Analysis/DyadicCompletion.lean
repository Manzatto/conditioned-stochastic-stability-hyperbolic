module

public import LeanShared.Analysis.DyadicCompactness
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Concrete norm completions of block cores

A completed space is the closed range of its actual block map inside a complete
block supremum space. Core density and the inherited norm are proved. A
continuous map agreeing with weak core blocks lifts canonically to the weak
closed range. No supplied Banach source or assumed compactness is needed.
-/

@[expose] public noncomputable section

open Set
open scoped ENNReal

namespace LeanShared.DyadicCompletion

section ClosedCore

variable {Core B F : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Completion of the actual block-core range, with its inherited norm. -/
def closedCore (q : Core →ₗ[ℂ] B) : Submodule ℂ B := q.range.topologicalClosure

instance closedCore_complete (q : Core →ₗ[ℂ] B) [CompleteSpace B] : CompleteSpace (closedCore q) := by
  unfold closedCore
  infer_instance

def coreLift (q : Core →ₗ[ℂ] B) : Core →ₗ[ℂ] closedCore q :=
  q.codRestrict (closedCore q) fun c => q.range.le_topologicalClosure ⟨c, rfl⟩

@[simp] theorem coe_coreLift (q : Core →ₗ[ℂ] B) (c : Core) :
    (coreLift q c : B) = q c := rfl

@[simp] theorem norm_coreLift (q : Core →ₗ[ℂ] B) (c : Core) : ‖coreLift q c‖ = ‖q c‖ := rfl

theorem coreLift_injective (q : Core →ₗ[ℂ] B) (hq : Function.Injective q) :
    Function.Injective (coreLift q) := by
  intro c d hcd
  exact hq (congrArg Subtype.val hcd)

/-- The smooth/block core is dense in its genuinely constructed completion. -/
theorem coreLift_dense (q : Core →ₗ[ℂ] B) : DenseRange (coreLift q) := by
  rw [DenseRange, Subtype.dense_iff]
  intro z hz
  apply closure_mono (s := range q) (t := (Subtype.val : closedCore q → B) '' range (coreLift q)) ?_ hz
  rintro b ⟨c, rfl⟩
  exact ⟨coreLift q c, ⟨c, rfl⟩, rfl⟩

variable (q : Core →ₗ[ℂ] B) (r : Core →ₗ[ℂ] F)
  (T : closedCore q →L[ℂ] F) (hagree : ∀ c : Core, T (coreLift q c) = r c)

include hagree in
/-- Agreement on the dense core forces the entire image into the weak completion. -/
theorem mapsTo_closedCore (z : closedCore q) : T z ∈ closedCore r := by
  refine (coreLift_dense q).induction_on (p := fun v => T v ∈ closedCore r) z
    ((r.range.isClosed_topologicalClosure).preimage T.continuous) ?_
  intro c
  rw [hagree]
  exact r.range.le_topologicalClosure ⟨c, rfl⟩

def lift : closedCore q →L[ℂ] closedCore r :=
  T.codRestrict (closedCore r) (mapsTo_closedCore q r T hagree)

@[simp] theorem coe_lift (z : closedCore q) : (lift q r T hagree z : F) = T z := rfl

theorem lift_core (c : Core) : lift q r T hagree (coreLift q c) = coreLift r c :=
  Subtype.ext (hagree c)

theorem lift_isCompact (hT : IsCompactOperator T) : IsCompactOperator (lift q r T hagree) :=
  hT.codRestrict (mapsTo_closedCore q r T hagree) r.range.isClosed_topologicalClosure

theorem lift_injective (hT : Function.Injective T) : Function.Injective (lift q r T hagree) := by
  intro x y hxy
  exact hT (congrArg Subtype.val hxy)

/-- Density also makes the extension canonical. -/
theorem lift_unique (S : closedCore q →L[ℂ] closedCore r)
    (hS : ∀ c : Core, S (coreLift q c) = coreLift r c) : S = lift q r T hagree := by
  apply ContinuousLinearMap.ext
  intro z
  refine (coreLift_dense q).induction_on (p := fun v => S v = lift q r T hagree v) z
    (isClosed_eq S.continuous (lift q r T hagree).continuous) ?_
  intro c
  rw [hS, lift_core]

end ClosedCore

section Dyadic

variable {Core F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

abbrev BlockSpace := DyadicCompactness.BlockSpace (F := F) (S := S)

def coordinate (j : ℕ × S) : BlockSpace (F := F) (S := S) →L[ℂ] F := lp.evalCLM ℂ _ ∞ j

theorem coordinate_norm_le (j : ℕ × S) : ‖coordinate (F := F) j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (one_mul ‖x‖).symm ▸ lp.norm_apply_le_norm ENNReal.top_ne_zero x j

/-- Genuine coordinate reweighting in the complete block supremum norm. -/
def reweight (η : ℝ) (hη : 0 < η) :
    BlockSpace (F := F) (S := S) →L[ℂ] BlockSpace (F := F) (S := S) :=
  DyadicCompactness.operator coordinate zero_le_one coordinate_norm_le
    (DyadicCompactness.dyadicFactor_pos η).le (DyadicCompactness.dyadicFactor_lt_one hη).le

@[simp] theorem reweight_apply (η : ℝ) (hη : 0 < η)
    (z : BlockSpace (F := F) (S := S)) (j : ℕ × S) :
    reweight η hη z j = ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) • z j := rfl

theorem reweight_injective (η : ℝ) (hη : 0 < η) :
    Function.Injective (reweight (F := F) (S := S) η hη) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : reweight η hη (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  apply lp.ext
  funext j
  have hj := congrArg (fun v => v j) hz
  rw [reweight_apply] at hj
  have hw : ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_pos (DyadicCompactness.dyadicFactor_pos η) _).ne'
  exact (smul_eq_zero.mp hj).resolve_left hw

variable (q : Core →ₗ[ℂ] BlockSpace (F := F) (S := S)) (η : ℝ) (hη : 0 < η)

/-- Actual weak core blocks, constructed from the same smooth core. -/
def weakCore : Core →ₗ[ℂ] BlockSpace (F := F) (S := S) := (reweight η hη).toLinearMap.comp q

/-- Canonical inclusion between the two explicitly constructed completions. -/
def inclusion : closedCore q →L[ℂ] closedCore (weakCore q η hη) :=
  lift q (weakCore q η hη) ((reweight η hη).comp (closedCore q).subtypeL) (fun _ => rfl)

@[simp] theorem inclusion_apply (z : closedCore q) (j : ℕ × S) :
    (inclusion q η hη z : BlockSpace (F := F) (S := S)) j =
      ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) • (z : BlockSpace (F := F) (S := S)) j := rfl

theorem inclusion_injective : Function.Injective (inclusion q η hη) := by
  apply lift_injective
  exact (reweight_injective η hη).comp Subtype.val_injective

theorem multiplier_bound (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    (x : BlockSpace (F := F) (S := S)) (j : ℕ × S) : ‖a j • x j‖ ≤ ‖x‖ := by
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ha j)).trans
    (lp.norm_apply_le_norm ENNReal.top_ne_zero x j)

def multiplierLinearMap (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1) :
    BlockSpace (F := F) (S := S) →ₗ[ℂ] BlockSpace (F := F) (S := S) where
  toFun x := ⟨fun j => a j • x j, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨j, rfl⟩
    exact multiplier_bound a ha x j⟩⟩
  map_add' x y := by
    apply lp.ext
    funext j
    exact smul_add _ _ _
  map_smul' c x := by
    apply lp.ext
    funext j
    exact smul_comm _ _ _

theorem multiplierLinearMap_norm_le (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    (x : BlockSpace (F := F) (S := S)) : ‖multiplierLinearMap a ha x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  exact lp.norm_le_of_forall_le (norm_nonneg x) (multiplier_bound a ha x)

/-- A genuine bounded coordinate multiplier, used for additional exponent loss. -/
def multiplier (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1) :
    BlockSpace (F := F) (S := S) →L[ℂ] BlockSpace (F := F) (S := S) :=
  (multiplierLinearMap a ha).mkContinuous 1 (multiplierLinearMap_norm_le a ha)

@[simp] theorem multiplier_apply (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    (x : BlockSpace (F := F) (S := S)) (j : ℕ × S) : multiplier a ha x j = a j • x j := rfl

theorem multiplier_injective (a : ℕ × S → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    (ha0 : ∀ j, a j ≠ 0) : Function.Injective (multiplier (F := F) a ha) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : multiplier a ha (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  apply lp.ext
  funext j
  have hj := congrArg (fun v => v j) hz
  change a j • (x - y) j = 0 at hj
  exact (smul_eq_zero.mp hj).resolve_left (ha0 j)

def branchWeight (δ : S → ℝ) (j : ℕ × S) : ℂ := ((2 : ℝ) ^ (-δ j.2 * j.1) : ℝ)

theorem branchWeight_norm_le (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) (j : ℕ × S) :
    ‖branchWeight δ j‖ ≤ 1 := by
  rw [branchWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hδ j.2)) (Nat.cast_nonneg _))

theorem branchWeight_ne_zero (δ : S → ℝ) (j : ℕ × S) : branchWeight δ j ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'

/-- Additional nonnegative exponent losses, possibly different in each branch. -/
def branchReweight (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    BlockSpace (F := F) (S := S) →L[ℂ] BlockSpace (F := F) (S := S) :=
  multiplier (branchWeight δ) (branchWeight_norm_le δ hδ)

def finalCore (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) : Core →ₗ[ℂ] BlockSpace (F := F) (S := S) :=
  (branchReweight δ hδ).toLinearMap.comp (weakCore q η hη)

def furtherInclusion (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    closedCore (weakCore q η hη) →L[ℂ] closedCore (finalCore q η hη δ hδ) :=
  lift (weakCore q η hη) (finalCore q η hη δ hδ)
    ((branchReweight δ hδ).comp (closedCore (weakCore q η hη)).subtypeL) (fun _ => rfl)

def exactInclusion (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    closedCore q →L[ℂ] closedCore (finalCore q η hη δ hδ) :=
  (furtherInclusion q η hη δ hδ).comp (inclusion q η hη)

theorem exactInclusion_apply (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)
    (z : closedCore q) (j : ℕ × S) :
    (exactInclusion q η hη δ hδ z : BlockSpace (F := F) (S := S)) j =
      (((2 : ℝ) ^ (-(η + δ j.2) * j.1) : ℝ) : ℂ) • (z : BlockSpace (F := F) (S := S)) j := by
  change branchWeight δ j • ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) •
    (z : BlockSpace (F := F) (S := S)) j = _
  rw [smul_smul, branchWeight, ← Complex.ofReal_mul]
  congr 2
  unfold DyadicCompactness.dyadicFactor
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

theorem exactInclusion_isCompact (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)
    (hcompact : IsCompactOperator (inclusion q η hη)) :
    IsCompactOperator (exactInclusion q η hη δ hδ) :=
  hcompact.clm_comp (furtherInclusion q η hη δ hδ)

theorem exactInclusion_injective (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    Function.Injective (exactInclusion q η hη δ hδ) := by
  have hf : Function.Injective (furtherInclusion q η hη δ hδ) := by
    apply lift_injective
    exact (multiplier_injective (branchWeight δ) (branchWeight_norm_le δ hδ)
      (branchWeight_ne_zero δ)).comp Subtype.val_injective
  exact hf.comp (inclusion_injective q η hη)

end Dyadic

end LeanShared.DyadicCompletion
