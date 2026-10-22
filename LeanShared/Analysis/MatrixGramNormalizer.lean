module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-! The inverse square root of the actual positive Gram matrix gives a
continuous normalization. This is a construction, not a continuous-frame
or metric-square-root assumption. -/
public noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace LeanShared.MatrixGramNormalizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def normalize (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := Ring.inverse (CFC.sqrt G)

theorem isUnit {G : Matrix ι ι ℝ} (positive : G.PosDef) : IsUnit (normalize G) := by
  have unit := (CFC.isUnit_sqrt_iff G positive.posSemidef.nonneg).mpr positive.isUnit
  obtain ⟨u,hu⟩ := unit
  change IsUnit (Ring.inverse (CFC.sqrt G))
  rw [←hu, Ring.inverse_unit]
  exact Units.isUnit _

theorem selfAdjoint {G : Matrix ι ι ℝ} (_positive : G.PosDef) : IsSelfAdjoint (normalize G) := by
  change star (Ring.inverse (CFC.sqrt G)) = Ring.inverse (CFC.sqrt G)
  rw [←Ring.inverse_star, (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq]

theorem identity {G : Matrix ι ι ℝ} (positive : G.PosDef) :
    star (normalize G)*G*normalize G = 1 := by
  have unit := (CFC.isUnit_sqrt_iff G positive.posSemidef.nonneg).mpr positive.isUnit
  have left := Ring.inverse_mul_cancel (CFC.sqrt G) unit
  have right := Ring.mul_inverse_cancel (CFC.sqrt G) unit
  rw [(selfAdjoint positive).star_eq]
  change Ring.inverse (CFC.sqrt G)*G*Ring.inverse (CFC.sqrt G) = 1
  calc
    _ = Ring.inverse (CFC.sqrt G)*(CFC.sqrt G*CFC.sqrt G)*Ring.inverse (CFC.sqrt G) :=
      congrArg (fun z => Ring.inverse (CFC.sqrt G)*z*Ring.inverse (CFC.sqrt G))
        (CFC.sqrt_mul_sqrt_self G positive.posSemidef.nonneg).symm
    _ = 1 := by rw [←mul_assoc, left, one_mul, right]

theorem continuousOn {X : Type*} [TopologicalSpace X] (K : Set X)
    (G : X → Matrix ι ι ℝ) (continuous : ContinuousOn G K)
    (positive : ∀ x ∈ K, (G x).PosDef) : ContinuousOn (fun x => normalize (G x)) K := by
  have sqrtContinuous : ContinuousOn (fun x => CFC.sqrt (G x)) K :=
    CFC.continuousOn_sqrt.comp continuous (fun x hx => (positive x hx).posSemidef.nonneg)
  intro x hx
  obtain ⟨u,hu⟩ := (CFC.isUnit_sqrt_iff (G x) (positive x hx).posSemidef.nonneg).mpr
    (positive x hx).isUnit
  have inverseAt : ContinuousAt (Ring.inverse : Matrix ι ι ℝ → Matrix ι ι ℝ) (CFC.sqrt (G x)) := by
    rw [←hu]
    exact NormedRing.inverse_continuousAt u
  exact inverseAt.comp_continuousWithinAt (f := fun y : X => CFC.sqrt (G y)) (sqrtContinuous x hx)

end LeanShared.MatrixGramNormalizer
