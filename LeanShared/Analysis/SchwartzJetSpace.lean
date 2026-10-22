module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Actual finite directional-derivative jets of supported smooth tests

The derivative word is a real directional derivative, complex-linear in the
test function. The jet subspace is the actual algebraic range of supported
Schwartz tests under their restricted derivative jets, with the inherited
finite-tuple supremum norm. No distribution representation is asserted.
-/

@[expose] public noncomputable section

open Set
open scoped SchwartzMap BoundedContinuousFunction LineDeriv

namespace LeanShared.SchwartzJetSpace

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An arbitrary ordered word of real directional derivatives on Schwartz space. -/
def wordDerivative : List E → 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)
  | [] => ContinuousLinearMap.id ℂ _
  | v :: w => (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) v).comp (wordDerivative w)

@[simp] theorem wordDerivative_nil (f : 𝓢(E, ℂ)) : wordDerivative [] f = f := rfl

@[simp] theorem wordDerivative_cons (v : E) (w : List E) (f : 𝓢(E, ℂ)) :
    wordDerivative (v :: w) f = ∂_{v} (wordDerivative w f) := rfl

/-- Each coordinate is a genuine iterated directional derivative restricted to `K`. -/
def jetMap (K : Set E) (w : I → List E) : 𝓢(E, ℂ) →ₗ[ℂ] (I → K →ᵇ ℂ) where
  toFun f i := (wordDerivative (w i) f).toBoundedContinuousFunction.domRestrict K
  map_add' f g := by
    funext i
    ext y
    change wordDerivative (w i) (f + g) y =
      wordDerivative (w i) f y + wordDerivative (w i) g y
    rw [map_add]
    rfl
  map_smul' c f := by
    funext i
    ext y
    change wordDerivative (w i) (c • f) y = c • wordDerivative (w i) f y
    rw [map_smul]
    rfl

@[simp] theorem jetMap_apply (K : Set E) (w : I → List E) (f : 𝓢(E, ℂ))
    (i : I) (y : K) : jetMap K w f i y = wordDerivative (w i) f y := rfl

/-- The genuine smooth test core supported in the given compact source.
Compactness of `K` is needed by the analytic consumers, not by this definition. -/
def supportedCore (K : Set E) : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | ∀ x ∉ K, f x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {f g} hf hg := by
    intro x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, zero_add]
  smul_mem' c f hf := by
    intro x hx
    change c • f x = 0
    rw [hf x hx, smul_zero]

/-- The actual finite jet subspace, with its inherited tuple norm. -/
def jetSpace (K : Set E) (w : I → List E) : Submodule ℂ (I → K →ᵇ ℂ) :=
  (jetMap K w).comp (supportedCore K).subtype |>.range

theorem jet_mem (K : Set E) (w : I → List E) (f : 𝓢(E, ℂ))
    (hf : ∀ x ∉ K, f x = 0) : jetMap K w f ∈ jetSpace K w :=
  ⟨⟨f, hf⟩, rfl⟩

/-- A derivative word does not enlarge the support of its smooth test. -/
theorem tsupport_wordDerivative_subset (w : List E) (f : 𝓢(E, ℂ)) :
    tsupport (wordDerivative w f) ⊆ tsupport f := by
  induction w with
  | nil => exact Subset.refl _
  | cons v w ih =>
      exact (SchwartzMap.tsupport_lineDerivOp_subset v (wordDerivative w f)).trans ih

end LeanShared.SchwartzJetSpace
