module

public import LeanShared.Analysis.DerivativeTransportFrames

/-!
# Actual inverse words on transported unstable fibers

Inverse words are constructed by reversing the actual successive inverse
maps. Their differentiated inverse identity gives the literal backward
derivative on the transported final fiber and the original initial fiber.
Thus the unstable inverse factor used by principal coefficients can be an
actual restricted inverse derivative rather than an unrelated scalar.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.TransportedInverseDerivative

open CylinderPrincipalCoefficient FiniteDerivativeWord DerivativeTransportFrames
open InvariantDerivativeCocycle

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def inversePrefix (B : G → E → E) {N : ℕ} (word : Fin N → G) : ℕ → E → E
  | 0 => id
  | k + 1 => if hk : k < N then inversePrefix B word k ∘ B (word ⟨k, hk⟩)
    else inversePrefix B word k

omit [FiniteDimensional ℝ E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem inversePrefix_left (F B : G → E → E) (hleft : ∀ a x, B a (F a x) = x)
    {N : ℕ} (word : Fin N → G) (k : ℕ) (x : E) :
    inversePrefix B word k (prefixOrbit F word k x) = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < N
    · simpa only [inversePrefix, prefixOrbit, dite_eq_left hk, Function.comp_apply, hleft] using ih
    · simpa only [inversePrefix, prefixOrbit, dite_eq_right hk] using ih

omit [FiniteDimensional ℝ E] in
theorem differentiable_inversePrefix (B : G → E → E) (hB : ∀ a, Differentiable ℝ (B a))
    {N : ℕ} (word : Fin N → G) (k : ℕ) : Differentiable ℝ (inversePrefix B word k) := by
  induction k with
  | zero => exact differentiable_id
  | succ k ih =>
    by_cases hk : k < N
    · simpa only [inversePrefix, dite_eq_left hk] using ih.comp (hB (word ⟨k, hk⟩))
    · simpa only [inversePrefix, dite_eq_right hk] using ih

omit [FiniteDimensional ℝ E] in
theorem inverse_fderiv_comp (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G) (k : ℕ) (x : E) :
    (fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)).comp
      (prefixDerivative F word x k) = ContinuousLinearMap.id ℝ E := by
  have hc := (differentiable_inversePrefix B hB word k _).hasFDerivAt.comp x
    (hasFDerivAt_prefixOrbit F hF word k x)
  have hid : HasFDerivAt (fun y => inversePrefix B word k (prefixOrbit F word k y))
      (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq (Eventually.of_forall (inversePrefix_left F B hleft word k))
  exact hc.unique hid

omit [FiniteDimensional ℝ E] in
theorem inverseDerivative_mapsTo_initial (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) :
    MapsTo (fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x))
      (transportedFiber F word x U₀ k) U₀ := by
  intro v hv
  obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp hv
  have hcomp := congrArg (fun A : E →L[ℝ] E => A u)
    (inverse_fderiv_comp F B hF hB hleft word k x)
  change fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)
    (prefixDerivative F word x k u) = u at hcomp
  rw [← he]
  change fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)
    (prefixDerivative F word x k u) ∈ U₀
  rw [hcomp]
  exact hu

def inverseUnstableFactor (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) : ℝ :=
  ‖(fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)).restrict
    (inverseDerivative_mapsTo_initial F B hF hB hleft word x U₀ k)‖

omit [FiniteDimensional ℝ E] in
/-- The constructed inverse unstable factor controls the minimal expansion
of the actual forward derivative on the initial unstable tangent fiber. -/
theorem norm_le_inverseUnstableFactor_mul (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U₀ : Submodule ℝ E) (k : ℕ) (v : E) (hv : v ∈ U₀) :
    ‖v‖ ≤ inverseUnstableFactor F B hF hB hleft word x U₀ k * ‖prefixDerivative F word x k v‖ := by
  let y : transportedFiber F word x U₀ k :=
    ⟨prefixDerivative F word x k v, Submodule.mem_map.mpr ⟨v, hv, rfl⟩⟩
  have hb := ((fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)).restrict
    (inverseDerivative_mapsTo_initial F B hF hB hleft word x U₀ k)).le_opNorm y
  change ‖fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)
    (prefixDerivative F word x k v)‖ ≤ inverseUnstableFactor F B hF hB hleft word x U₀ k *
      ‖prefixDerivative F word x k v‖ at hb
  have he := congrArg (fun A : E →L[ℝ] E => A v)
    (inverse_fderiv_comp F B hF hB hleft word k x)
  change fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)
    (prefixDerivative F word x k v) = v at he
  rw [he] at hb
  exact hb

end LeanShared.TransportedInverseDerivative
