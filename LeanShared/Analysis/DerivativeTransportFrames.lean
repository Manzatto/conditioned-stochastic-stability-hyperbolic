module

public import LeanShared.Analysis.TangentDerivativePositivity

/-!
# Constructed transported tangent fibers and isometric frames

Transport is the image of the initial tangent subspace under the actual
derivative of the chronological prefix word. The actual inverse-map identity
proves injectivity and dimension preservation. Standard orthonormal bases
then construct the isometric frames required by the intrinsic-Jacobian
product theorem; neither noisy bundle invariance nor frames are supplied.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.DerivativeTransportFrames

open CylinderPrincipalCoefficient FiniteDerivativeWord TransportedTangentWord

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def transportedFiber (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) : Submodule ℝ E :=
  U₀.map (prefixDerivative F word x k).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem transportedFiber_step (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) (hk : k < N) :
    MapsTo (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x))
      (transportedFiber F word x U₀ k) (transportedFiber F word x U₀ (k + 1)) := by
  intro v hv
  obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp hv
  apply Submodule.mem_map.mpr
  refine ⟨u, hu, ?_⟩
  simp only [prefixDerivative, dite_eq_left hk, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) he

omit [FiniteDimensional ℝ E] in
theorem prefixDerivative_injective (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G) (x : E) (k : ℕ) :
    Function.Injective (prefixDerivative F word x k) := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih =>
    by_cases hk : k < N
    · simp only [prefixDerivative, dite_eq_left hk, ContinuousLinearMap.coe_comp]
      exact (fderiv_injective_of_local_inverse (F (word ⟨k, hk⟩)) (B (word ⟨k, hk⟩))
        (prefixOrbit F word k x) (hF _ _) (hB _ _) (Eventually.of_forall (hleft _))).comp ih
    · simpa only [prefixDerivative, dite_eq_right hk] using ih

def transportFrame (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) : U₀ ≃ₗᵢ[ℝ] transportedFiber F word x U₀ k := by
  have hdim : Module.finrank ℝ (transportedFiber F word x U₀ k) = Module.finrank ℝ U₀ :=
    (Submodule.equivMapOfInjective (prefixDerivative F word x k).toLinearMap
      (prefixDerivative_injective F B hF hB hleft word x k) U₀).finrank_eq.symm
  exact (stdOrthonormalBasis ℝ U₀).repr.trans
    ((stdOrthonormalBasis ℝ (transportedFiber F word x U₀ k)).reindex (finCongr hdim)).repr.symm

/-- Actual diffeomorphisms and an initial subspace produce every transport/frame input to the
intrinsic finite-word Jacobian identity. -/
theorem normDet_transported_word (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) (hk : k ≤ N) :
    ((prefixDerivative F word x k).restrict
      (prefixDerivative_mapsTo F word x (transportedFiber F word x U₀)
        (transportedFiber_step F word x U₀) k hk)).toLinearMap.normDet =
      tangentJacobianProduct F word x (transportedFiber F word x U₀)
        (transportedFiber_step F word x U₀) k :=
  normDet_prefixDerivative F word x (transportedFiber F word x U₀)
    (transportFrame F B hF hB hleft word x U₀) (transportedFiber_step F word x U₀) k hk

end LeanShared.DerivativeTransportFrames
