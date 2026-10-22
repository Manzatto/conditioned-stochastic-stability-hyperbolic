module

public import LeanShared.Analysis.FractionalDerivativeBounds
public import LeanShared.Analysis.WordHyperbolicityFactors

/-!
# Quantitative parameters for the cited local microlocal kernel estimate

Baladi--Tsujii (2007), §3 (12), §6 (19), (27), (29)--(31), and
Baladi--Tsujii (2008), Lemma 4.14 (4.26), bound the off-diagonal kernel
using finite derivative norms, the top fractional Hölder seminorm, fixed
coordinate supports/cutoffs and a positive phase-gradient gap.
Uniformity on sets with bounded parameters is a consequence of that
kernel proof, not a source statement asserting semicontinuity of an
arbitrary constant `C(T,G)`.

The parameters below refer to the literal finite composition, literal
inverse composition, accumulated weight and actual derivative phase.
Classical finite `C^r` composition estimates can supply the uniform norm
bounds. The phase-gap neighborhood is constructed in
`RobustFrequencySeparation`. A kernel estimate must still identify the
dyadic nonlinked relation and fixed cutoffs with the source conventions.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.MicrolocalBlockParameters

open CylinderPrincipalCoefficient FiniteDerivativeWord TransportedInverseDerivative
open FractionalDerivativeBounds

structure Parameters where
  mapBound : ℝ
  inverseBound : ℝ
  weightBound : ℝ
  phaseGap : ℝ
  map_nonneg : 0 ≤ mapBound
  inverse_nonneg : 0 ≤ inverseBound
  weight_nonneg : 0 ≤ weightBound
  gap_pos : 0 < phaseGap

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- For `r=m+delta`, map and inverse have order `m+delta`, while the
weight has order `m-1+delta`. The highest increments are retained. -/
structure Controls (F B : G → E → E) (g : E → ℝ)
    (K L : Set E) (m : ℕ) (δ : ℝ) {N : ℕ} (word : Fin N → G)
    (nonlinked : E → E → ℝ → Prop) (p : Parameters) : Prop where
  order_pos : 0 < m
  fraction_nonneg : 0 ≤ δ
  fraction_lt_one : δ < 1
  map : Bounds (prefixOrbit F word N) K m δ p.mapBound
  inverse : Bounds (inversePrefix B word N) L m δ p.inverseBound
  weight : Bounds (fun x => wordWeight F g (word, x)) K (m - 1) δ p.weightBound
  phase : ∀ x ∈ K, ∀ ξ η Λ, nonlinked ξ η Λ → 0 ≤ Λ →
    p.phaseGap * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint (prefixDerivative F word x N) η‖

end LeanShared.MicrolocalBlockParameters
