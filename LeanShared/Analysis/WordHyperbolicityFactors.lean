module

public import LeanShared.Analysis.TransportedInverseDerivative

/-!
# Literal geometric factors for a finite-word principal density

The stable factor restricts the actual derivative to the preimage of the
endpoint stable fiber. This matches the off-core definition of local stable
expansion without assuming the extended stable bundle is invariant. The
unstable Jacobian restricts to the initial unstable fiber, transported by the
actual derivative. The inverse unstable factor is the norm of the literal
inverse-word derivative on that transported fiber.

All factors are constructed from maps and tangent subspaces.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.WordHyperbolicityFactors

open CylinderPrincipalCoefficient FiniteDerivativeWord DerivativeTransportFrames
open TransportedInverseDerivative

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def stableInitialFiber (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (endpoint : Submodule ℝ E) (k : ℕ) : Submodule ℝ E :=
  endpoint.comap (prefixDerivative F word x k).toLinearMap

def stableFactor (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (endpoint : Submodule ℝ E) (k : ℕ) : ℝ :=
  ‖(prefixDerivative F word x k).restrict
    (show MapsTo (prefixDerivative F word x k)
      (stableInitialFiber F word x endpoint k) endpoint from fun _ hv => hv)‖

def unstableJacobian (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (initial : Submodule ℝ E) (k : ℕ) : ℝ :=
  ((prefixDerivative F word x k).restrict
    (show MapsTo (prefixDerivative F word x k) initial
      (transportedFiber F word x initial k) from
        fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)).toLinearMap.normDet

theorem unstableJacobian_pos (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (initial : Submodule ℝ E) (k : ℕ) : 0 < unstableJacobian F word x initial k := by
  have hinj := prefixDerivative_injective F B hF hB hleft word x k
  let A := (prefixDerivative F word x k).restrict
    (show MapsTo (prefixDerivative F word x k) initial
      (transportedFiber F word x initial k) from
        fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  have hA : Function.Injective A.toLinearMap := by
    intro u v huv
    apply Subtype.ext
    exact hinj (congrArg Subtype.val huv)
  have hne := (A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hA
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hne)

/-- The geometric principal density consumed by the cylinder interface,
with literal maps, accumulated weights and actual derivative restrictions. -/
def geometricPrincipalDensity (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) (g : E → ℝ)
    (stable unstable : E → Submodule ℝ E) (N : ℕ) (t s : ℝ) :
    (Fin N → G) × E → ℝ :=
  principalDensity (wordWeight F g)
    (fun z => unstableJacobian F z.1 z.2 (unstable z.2) N)
    (fun z => stableFactor F z.1 z.2 (stable (prefixOrbit F z.1 N z.2)) N)
    (fun z => inverseUnstableFactor F B hF hB hleft z.1 z.2 (unstable z.2) N) t s

end LeanShared.WordHyperbolicityFactors
