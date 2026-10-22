module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RankOneRetraction
public import Mathlib.Topology.ContinuousMap.Compact

/-! Concrete bounded-continuous tensor lift and partial eigenfunctional.
These are the actual retraction maps for an independent auxiliary factor. -/

@[expose] public noncomputable section
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- Freeze the original state, keeping the auxiliary coordinate live. -/
def sectionAt (h : X × Y →ᵇ ℝ) (x : X) : Y →ᵇ ℝ :=
  h.compContinuous ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

omit [CompactSpace X] [CompactSpace Y] in
@[simp] theorem sectionAt_apply (h : X × Y →ᵇ ℝ) (x : X) (y : Y) :
    sectionAt h x y = h (x, y) := rfl

omit [CompactSpace X] in
theorem continuous_sectionAt (h : X × Y →ᵇ ℝ) : Continuous (sectionAt h) := by
  have hc := (ContinuousMap.linearIsometryBoundedOfCompact Y ℝ ℝ).continuous.comp
    h.toContinuousMap.curry.continuous
  convert hc using 1
  ext x y
  rfl

/-- Multiply a function on the original space by the auxiliary eigenvector. -/
def tensorLift (g : Y →ᵇ ℝ) : (X →ᵇ ℝ) →L[ℝ] (X × Y →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.compContinuous ⟨Prod.fst, continuous_fst⟩ *
        g.compContinuous ⟨Prod.snd, continuous_snd⟩
      map_add' := by intro f h; ext z; simp [add_mul]
      map_smul' := by intro c f; ext z; simp; ring }
    ‖g‖ (fun f => by
      calc
        _ ≤ ‖f.compContinuous ⟨Prod.fst, continuous_fst⟩‖ *
            ‖g.compContinuous ⟨Prod.snd, continuous_snd⟩‖ := norm_mul_le _ _
        _ ≤ ‖f‖ * ‖g‖ := mul_le_mul
          (BoundedContinuousFunction.norm_compContinuous_le _ _)
          (BoundedContinuousFunction.norm_compContinuous_le _ _)
          (norm_nonneg _) (norm_nonneg _)
        _ = _ := mul_comm _ _)

omit [CompactSpace X] [CompactSpace Y] in
@[simp] theorem tensorLift_apply (g : Y →ᵇ ℝ) (f : X →ᵇ ℝ) (x : X) (y : Y) :
    tensorLift g f (x, y) = f x * g y := rfl

def partialValue (l : (Y →ᵇ ℝ) →L[ℝ] ℝ) (h : X × Y →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => l (sectionAt h x), l.continuous.comp (continuous_sectionAt h)⟩

/-- Apply the auxiliary left eigenfunctional at each original state. -/
def partialMean (l : (Y →ᵇ ℝ) →L[ℝ] ℝ) : (X × Y →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := partialValue l
      map_add' := by
        intro f h
        ext x
        change l (sectionAt (f + h) x) = _
        have he : sectionAt (f + h) x = sectionAt f x + sectionAt h x := by ext y; rfl
        rw [he, map_add]
        rfl
      map_smul' := by
        intro c h
        ext x
        change l (sectionAt (c • h) x) = _
        have he : sectionAt (c • h) x = c • sectionAt h x := by ext y; rfl
        rw [he, map_smul]
        rfl }
    ‖l‖ (fun h => by
      change ‖partialValue l h‖ ≤ ‖l‖ * ‖h‖
      apply (BoundedContinuousFunction.norm_le (f := partialValue l h)
        (C := ‖l‖ * ‖h‖) (mul_nonneg (norm_nonneg l) (norm_nonneg h))).mpr
      intro x
      exact (l.le_opNorm (sectionAt h x)).trans
        (mul_le_mul_of_nonneg_left
          (BoundedContinuousFunction.norm_compContinuous_le _ _) (norm_nonneg _)))

@[simp] theorem partialMean_apply (l : (Y →ᵇ ℝ) →L[ℝ] ℝ)
    (h : X × Y →ᵇ ℝ) (x : X) : partialMean l h x = l (sectionAt h x) := rfl

/-- The eigenpair normalization gives an exact left inverse. -/
theorem partialMean_tensorLift (l : (Y →ᵇ ℝ) →L[ℝ] ℝ) (g : Y →ᵇ ℝ)
    (hn : l g = 1) :
    (partialMean l).comp (tensorLift (X := X) g) = ContinuousLinearMap.id ℝ (X →ᵇ ℝ) := by
  ext f x
  change l (sectionAt (tensorLift g f) x) = f x
  have he : sectionAt (tensorLift g f) x = f x • g := by ext y; rfl
  rw [he, map_smul, hn]
  simp

end ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction
