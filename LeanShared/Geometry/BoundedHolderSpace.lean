module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import LeanShared.Analysis.DyadicCompletion

/-! A concrete Banach space of bounded Hölder functions, realized as the
closed graph of their difference quotient in two bounded continuous function
spaces. Smooth-core closures give little Hölder spaces without falsely
claiming density in the full Hölder space. -/

@[expose] public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedHolderSpace
variable (X : Type*) [MetricSpace X]

abbrev Pairs := {p : X × X // p.1 ≠ p.2}
abbrev Ambient := (X →ᵇ ℂ) × (Pairs X →ᵇ ℂ)

def weight (u : ℝ) (p : Pairs X) : ℂ := (dist p.val.1 p.val.2 ^ u : ℝ)

def graph (u : ℝ) : Submodule ℂ (Ambient X) where
  carrier := {v | ∀ p, v.2 p * weight X u p = v.1 p.val.1 - v.1 p.val.2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb p
    change (a.2 p + b.2 p) * weight X u p =
      (a.1 p.val.1 + b.1 p.val.1) - (a.1 p.val.2 + b.1 p.val.2)
    rw [add_mul, ha p, hb p]
    ring
  smul_mem' := by
    intro c a ha p
    change (c * a.2 p) * weight X u p = c * a.1 p.val.1 - c * a.1 p.val.2
    rw [mul_assoc, ha p]
    ring

theorem graph_closed (u : ℝ) : IsClosed (graph X u : Set (Ambient X)) := by
  change IsClosed {v : Ambient X | ∀ p, v.2 p * weight X u p = v.1 p.val.1 - v.1 p.val.2}
  have eq : {v : Ambient X | ∀ p, v.2 p * weight X u p = v.1 p.val.1 - v.1 p.val.2} =
      ⋂ p, {v : Ambient X | v.2 p * weight X u p = v.1 p.val.1 - v.1 p.val.2} := by
    ext v
    simp
  rw [eq]
  apply isClosed_iInter
  intro p
  apply isClosed_eq
  · exact ((BoundedContinuousFunction.evalCLM ℂ p).continuous.comp continuous_snd).mul continuous_const
  · exact ((BoundedContinuousFunction.evalCLM ℂ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℂ p.val.2).continuous.comp continuous_fst)

instance graph_complete (u : ℝ) : CompleteSpace (graph X u) :=
  (graph_closed X u).completeSpace_coe

def physical (u : ℝ) : graph X u →L[ℂ] (X →ᵇ ℂ) :=
  (ContinuousLinearMap.fst ℂ (X →ᵇ ℂ) (Pairs X →ᵇ ℂ)).comp (graph X u).subtypeL

theorem physical_injective (u : ℝ) : Function.Injective (physical X u) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact hab
  · apply BoundedContinuousFunction.ext
    intro p
    have hw : weight X u p ≠ 0 := by
      unfold weight
      exact_mod_cast (Real.rpow_pos_of_pos (dist_pos.mpr p.property) u).ne'
    apply mul_right_cancel₀ hw
    rw [a.property p, b.property p]
    change (physical X u a) p.val.1 - (physical X u a) p.val.2 =
      (physical X u b) p.val.1 - (physical X u b) p.val.2
    rw [hab]

theorem physical_norm_le (u : ℝ) (v : graph X u) : ‖physical X u v‖ ≤ ‖v‖ :=
  norm_fst_le v.val

theorem increment_bound (u : ℝ) (v : graph X u) (x y : X) :
    ‖physical X u v x - physical X u v y‖ ≤ ‖v‖ * dist x y ^ u := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (dist_nonneg) _)
  · let p : Pairs X := ⟨(x, y), hxy⟩
    have hv := v.property p
    change v.val.2 p * weight X u p = _ at hv
    change ‖v.val.1 x - v.val.1 y‖ ≤ _
    rw [← hv, norm_mul]
    have hw : ‖weight X u p‖ = dist x y ^ u := by
      simp only [weight, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)
    rw [hw]
    exact mul_le_mul_of_nonneg_right
      ((v.val.2.norm_coe_le_norm p).trans (norm_snd_le v.val))
      (Real.rpow_nonneg dist_nonneg _)

/-- The actual little regular space for a chosen smooth test core is its
closed range in the concrete Hölder Banach space. -/
def little {Core : Type*} [AddCommGroup Core] [Module ℂ Core]
    (u : ℝ) (q : Core →ₗ[ℂ] graph X u) : Submodule ℂ (graph X u) :=
  DyadicCompletion.closedCore q

end LeanShared.BoundedHolderSpace
