module
public import LeanShared.Geometry.BoundedHolderCore
public import LeanShared.Analysis.HolderInterpolation
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! A literal weighted composition is bounded in the actual Hölder graph
norm. The constants come from an ordinary Lipschitz map and a genuinely Hölder weight; no derivative of the weight is required. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.HolderWeightComposition
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {a : ℝ} (ha : 0≤a)
  (ψ : X →ᵇ ℂ) {Cψ : ℝ} (hCψ : 0≤Cψ)
  (holderψ : ∀x y,‖ψ x-ψ y‖≤Cψ*dist x y^a) {Lg : NNReal}
  (g : X → Y) (lipg : LipschitzWith Lg g)

@[expose] def functions : BoundedHolderSpace.graph Y a →ₗ[ℂ] (X →ᵇ ℂ) where
  toFun v := ψ * (BoundedHolderSpace.physical Y a v).compContinuous ⟨g,lipg.continuous⟩
  map_add' f h := by
    ext x
    change ψ x*(BoundedHolderSpace.physical Y a (f+h) (g x)) =
      ψ x*(BoundedHolderSpace.physical Y a f (g x)) + ψ x*(BoundedHolderSpace.physical Y a h (g x))
    rw [map_add]
    change ψ x*((BoundedHolderSpace.physical Y a f (g x)) + (BoundedHolderSpace.physical Y a h (g x))) = _
    ring
  map_smul' z f := by
    ext x
    change ψ x*(BoundedHolderSpace.physical Y a (z • f) (g x)) =
      z*(ψ x*(BoundedHolderSpace.physical Y a f (g x)))
    rw [map_smul]
    change ψ x*(z*(BoundedHolderSpace.physical Y a f (g x))) = _
    ring

include ha hCψ holderψ in
theorem increment (v : BoundedHolderSpace.graph Y a) (x y : X) :
    ‖functions ψ g lipg v x-functions ψ g lipg v y‖ ≤
      (‖ψ‖*(Lg:ℝ)^a + Cψ)*‖v‖*dist x y^a := by
  let f := BoundedHolderSpace.physical Y a v
  have split : ψ x*f (g x)-ψ y*f (g y) =
      ψ x*(f (g x)-f (g y))+(ψ x-ψ y)*f (g y) := by ring
  have compose := (BoundedHolderSpace.increment_bound Y a v (g x) (g y)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (lipg.dist_le_mul x y) ha) (norm_nonneg v))
  rw [Real.mul_rpow Lg.coe_nonneg dist_nonneg] at compose
  have weight := holderψ x y
  have value : ‖f (g y)‖≤‖v‖ := (f.norm_coe_le_norm _).trans (BoundedHolderSpace.physical_norm_le Y a v)
  change ‖ψ x*f (g x)-ψ y*f (g y)‖ ≤ _
  rw [split]
  calc
    _ ≤ ‖ψ x*(f (g x)-f (g y))‖+‖(ψ x-ψ y)*f (g y)‖ := norm_add_le _ _
    _ ≤ ‖ψ‖*(‖v‖*((Lg:ℝ)^a*dist x y^a))+
        (Cψ*dist x y^a)*‖v‖ := by
      rw [norm_mul,norm_mul]
      exact add_le_add
        (mul_le_mul (ψ.norm_coe_le_norm x) compose (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul weight value (norm_nonneg _) (by positivity))
    _ = _ := by ring
theorem functions_norm (v : BoundedHolderSpace.graph Y a) :
    ‖functions ψ g lipg v‖ ≤ ‖ψ‖*‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  change ‖ψ x * (BoundedHolderSpace.physical Y a v) (g x)‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (ψ.norm_coe_le_norm x)
    (((BoundedHolderSpace.physical Y a v).norm_coe_le_norm _).trans
      (BoundedHolderSpace.physical_norm_le Y a v)) (norm_nonneg _) (norm_nonneg _)

@[expose] def lifted : BoundedHolderSpace.graph Y a →ₗ[ℂ] BoundedHolderSpace.graph X a :=
  BoundedHolderSpace.liftCore X a (functions ψ g lipg)
    (fun v => ⟨(‖ψ‖*(Lg:ℝ)^a + Cψ)*‖v‖,
      increment ha ψ hCψ holderψ g lipg v⟩)

include ha hCψ holderψ in
theorem lifted_norm (v : BoundedHolderSpace.graph Y a) :
    ‖lifted ha ψ hCψ holderψ g lipg v‖ ≤
      max ‖ψ‖ (‖ψ‖*(Lg:ℝ)^a + Cψ)*‖v‖ := by
  have nonnegative : 0≤‖ψ‖*(Lg:ℝ)^a + Cψ := by positivity
  have graphBound := HolderInterpolation.graph_norm_le a (lifted ha ψ hCψ holderψ g lipg v)
    (mul_nonneg nonnegative (norm_nonneg v)) (increment ha ψ hCψ holderψ g lipg v)
  apply graphBound.trans
  apply max_le
  · exact (functions_norm ψ g lipg v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)

@[expose] def operator : BoundedHolderSpace.graph Y a →L[ℂ] BoundedHolderSpace.graph X a :=
  (lifted ha ψ hCψ holderψ g lipg).mkContinuous
    (max ‖ψ‖ (‖ψ‖*(Lg:ℝ)^a + Cψ))
    (lifted_norm ha ψ hCψ holderψ g lipg)

/-- The constructed operator is literally the weighted composition at every point. -/
theorem physical_operator (v : BoundedHolderSpace.graph Y a) (x : X) :
    BoundedHolderSpace.physical X a (operator ha ψ hCψ holderψ g lipg v) x =
      ψ x * BoundedHolderSpace.physical Y a v (g x) := rfl
end LeanShared.HolderWeightComposition
