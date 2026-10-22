module

public import LeanShared.Analysis.ActualWordWeightProduct
public import LeanShared.Analysis.ActualWordChronology

/-! Joint continuity of the literal accumulated weight uses only joint
continuity of the actual maps and continuity of the actual scalar weight.
No parameter continuity in the top fractional C^r norm is required. -/

public noncomputable section
open scoped BigOperators
namespace LeanShared.ActualWordWeightContinuity
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]

theorem continuous_weight (F : G → X → X)
    (hF : Continuous (fun z : G × X => F z.1 z.2)) (g : X → ℝ) (hg : Continuous g) (N : ℕ) :
    Continuous (fun z : (Fin N → G) × X => IntrinsicPrincipalDensity.weight F g (List.ofFn z.1) z.2) := by
  have heq : (fun z : (Fin N → G) × X => IntrinsicPrincipalDensity.weight F g (List.ofFn z.1) z.2) =
      (fun z => ∏ j : Fin N, g (CylinderPrincipalCoefficient.prefixOrbit F z.1 j.val z.2)) := by
    funext z
    exact ActualWordWeightProduct.intrinsic_weight_eq_product F g z.1 z.2
  rw [heq]
  exact continuous_finsetProd _ (fun j _ => hg.comp
    (CylinderPrincipalCoefficient.continuous_prefixOrbit F hF N j.val))

end LeanShared.ActualWordWeightContinuity
