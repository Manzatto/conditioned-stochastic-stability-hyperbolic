module

public import LeanShared.Analysis.DyadicCompletion
public import LeanShared.Analysis.CompactnessFromComponents
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Finite chart assembly on actual core completions

The global chart norm is the inherited finite-product maximum norm. Compact
local operators yield a compact product operator by finite coordinate control;
local injectivity yields global injectivity. The actual weak core is the image
of the explicit strong core map under that operator. Its closure map is then
constructed, with core agreement and uniqueness, rather than supplied.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace LeanShared.FiniteChartCompletion

open DyadicCompletion

variable {I Core : Type*} [Fintype I] [AddCommGroup Core] [Module ℂ Core]
  {B F : I → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  (T : ∀ i, B i →L[ℂ] F i)

/-- The actual finite chart product operator. -/
def product : (∀ i, B i) →L[ℂ] (∀ i, F i) :=
  ContinuousLinearMap.pi fun i => (T i).comp (ContinuousLinearMap.proj i)

omit [Fintype I] in
@[simp]
theorem product_apply (x : ∀ i, B i) (i : I) : product T x i = T i (x i) := rfl

omit [Fintype I] in
/-- Coordinatewise injectivity suffices; no global injectivity is assumed. -/
theorem product_injective (hinj : ∀ i, Function.Injective (T i)) :
    Function.Injective (product T) := by
  intro x y hxy
  funext i
  apply hinj i
  exact congrArg (fun z => z i) hxy

/-- Finite compact coordinate control proves compactness of the actual
product map in its maximum norm. -/
theorem product_isCompact [∀ i, CompleteSpace (F i)]
    (hcompact : ∀ i, IsCompactOperator (T i)) : IsCompactOperator (product T) := by
  classical
  apply CompactnessFromComponents.isCompactOperator_of_finite_components
    (product T) (fun i => (T i).comp (ContinuousLinearMap.proj i))
    (fun i => (hcompact i).comp_clm (ContinuousLinearMap.proj i))
  intro ε hε
  refine ⟨Finset.univ, ε, hε, ?_⟩
  intro x _ y _ hxy
  apply (dist_pi_lt_iff hε).mpr
  intro i
  exact hxy i (Finset.mem_univ i)

variable (q : Core →ₗ[ℂ] (∀ i, B i))

/-- The strong completion inherits exactly the finite maximum chart norm,
with value zero for an empty chart family. -/
theorem core_norm (c : Core) :
    ‖coreLift q c‖ = ((Finset.univ.sup (fun i => ‖q c i‖₊) : ℝ≥0) : ℝ) := rfl

/-- The actual weak chart core, using precisely the same smooth functions. -/
def weakCore : Core →ₗ[ℂ] (∀ i, F i) := (product T).toLinearMap.comp q

omit [Fintype I] in
@[simp]
theorem weakCore_apply (c : Core) (i : I) : weakCore T q c i = T i (q c i) := rfl

/-- The constructed closure map for the finite chart maximum norm. -/
def inclusion : closedCore q →L[ℂ] closedCore (weakCore T q) :=
  DyadicCompletion.lift q (weakCore T q)
    ((product T).comp (closedCore q).subtypeL) (fun _ => rfl)

@[simp]
theorem inclusion_apply (x : closedCore q) (i : I) :
    (inclusion T q x : ∀ i, F i) i = T i (x.val i) := rfl

/-- The weak norm is the exact finite maximum of the local transferred
chart norms, rather than a supplied norm-comparison assumption. -/
theorem inclusion_norm (x : closedCore q) :
    ‖inclusion T q x‖ = ((Finset.univ.sup (fun i => ‖T i (x.val i)‖₊) : ℝ≥0) : ℝ) := rfl

@[simp]
theorem inclusion_core (c : Core) :
    inclusion T q (coreLift q c) = coreLift (weakCore T q) c :=
  DyadicCompletion.lift_core q (weakCore T q)
    ((product T).comp (closedCore q).subtypeL) (fun _ => rfl) c

theorem inclusion_injective (hinj : ∀ i, Function.Injective (T i)) :
    Function.Injective (inclusion T q) := by
  apply DyadicCompletion.lift_injective
  exact (product_injective T hinj).comp Subtype.val_injective

theorem inclusion_isCompact [∀ i, CompleteSpace (F i)]
    (hcompact : ∀ i, IsCompactOperator (T i)) : IsCompactOperator (inclusion T q) := by
  apply DyadicCompletion.lift_isCompact
  exact (product_isCompact T hcompact).comp_clm (closedCore q).subtypeL

/-- Agreement with all chart core functions determines the entire inclusion. -/
theorem inclusion_unique (S : closedCore q →L[ℂ] closedCore (weakCore T q))
    (hS : ∀ c, S (coreLift q c) = coreLift (weakCore T q) c) : S = inclusion T q :=
  DyadicCompletion.lift_unique q (weakCore T q)
    ((product T).comp (closedCore q).subtypeL) (fun _ => rfl) S hS

end LeanShared.FiniteChartCompletion
