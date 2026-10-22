module

public import LeanShared.Geometry.SmoothHolderTestSpaces
public import LeanShared.Geometry.SupportedCoreMultipliers

/-! Multiplication is bounded in the concrete Hölder graph norm. The
increment coordinate is constructed algebraically, so no regularity or
linearity of chosen quotient representatives is assumed. -/

@[expose] public noncomputable section
open Set
open scoped BoundedContinuousFunction Manifold ContDiff
namespace LeanShared.BoundedHolderSpace
variable {X : Type*} [MetricSpace X] (u : ℝ)

def firstPair : C(Pairs X, X) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩
def secondPair : C(Pairs X, X) :=
  ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

def product (a b : graph X u) : graph X u :=
  ⟨(a.val.1 * b.val.1,
    a.val.1.compContinuous firstPair * b.val.2 +
      b.val.1.compContinuous secondPair * a.val.2), by
    intro p
    change (a.val.1 p.val.1 * b.val.2 p + b.val.1 p.val.2 * a.val.2 p) * weight X u p =
      a.val.1 p.val.1 * b.val.1 p.val.1 - a.val.1 p.val.2 * b.val.1 p.val.2
    calc
      _ = a.val.1 p.val.1 * (b.val.2 p * weight X u p) +
          b.val.1 p.val.2 * (a.val.2 p * weight X u p) := by ring
      _ = _ := by rw [a.property p, b.property p]; ring⟩

@[simp] theorem physical_product (a b : graph X u) :
    physical X u (product u a b) = physical X u a * physical X u b := rfl

theorem product_norm_le (a b : graph X u) :
    ‖product u a b‖ ≤ (2 * ‖a‖) * ‖b‖ := by
  change ‖(product u a b).val‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_mul_le a.val.1 b.val.1).trans (by
      have ha := norm_fst_le a.val
      have hb := norm_fst_le b.val
      change ‖a.val.1‖ ≤ ‖a‖ at ha
      change ‖b.val.1‖ ≤ ‖b‖ at hb
      nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b),
        mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)])
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro p
    change ‖a.val.1 p.val.1 * b.val.2 p + b.val.1 p.val.2 * a.val.2 p‖ ≤ _
    have ha1 := (a.val.1.norm_coe_le_norm p.val.1).trans (norm_fst_le a.val)
    have ha2 := (a.val.2.norm_coe_le_norm p).trans (norm_snd_le a.val)
    have hb1 := (b.val.1.norm_coe_le_norm p.val.2).trans (norm_fst_le b.val)
    have hb2 := (b.val.2.norm_coe_le_norm p).trans (norm_snd_le b.val)
    exact (norm_add_le _ _).trans ((add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul ha1 hb2 (norm_nonneg _) (norm_nonneg _)))
      ((norm_mul_le _ _).trans (mul_le_mul hb1 ha2 (norm_nonneg _) (norm_nonneg _)))).trans
      (by ring_nf; exact le_rfl))

def multiplyLinear (a : graph X u) : graph X u →ₗ[ℂ] graph X u where
  toFun b := product u a b
  map_add' b c := by
    apply physical_injective X u
    simp only [physical_product, (physical X u).map_add, mul_add]
  map_smul' c b := by
    apply physical_injective X u
    simp only [physical_product, (physical X u).map_smul]
    ext x
    change (physical X u a) x * (c * (physical X u b) x) =
      c * ((physical X u a) x * (physical X u b) x)
    ring

def multiply (a : graph X u) : graph X u →L[ℂ] graph X u :=
  (multiplyLinear u a).mkContinuous (2 * ‖a‖) (product_norm_le u a)

end LeanShared.BoundedHolderSpace

namespace LeanShared.SmoothHolderTestSpaces
open SmoothSupportedManifoldCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M]
  (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

/-- Smooth multiplication has a derived bound in the actual supported
little Hölder norm, with one constant for all smooth input vectors. -/
theorem smooth_multiplier_bound (V : Set M) (ψ : M → ℂ)
    (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ) :
    ∃ B : ℝ, ∀ c : core (E := E) V,
      ‖coreMap u holder V (multiplier V ψ hψ c)‖ ≤ B * ‖coreMap u holder V c‖ := by
  let d : core (E := E) (univ : Set M) := ⟨ψ, hψ, subset_univ _⟩
  let a := holderCore u holder univ d
  refine ⟨2 * ‖a‖, ?_⟩
  intro c
  have hid : holderCore u holder V (multiplier V ψ hψ c) =
      BoundedHolderSpace.product u a (holderCore u holder V c) := by
    apply BoundedHolderSpace.physical_injective M u
    ext x
    change c.val x * ψ x = ψ x * c.val x
    exact mul_comm _ _
  change ‖holderCore u holder V (multiplier V ψ hψ c)‖ ≤
    (2 * ‖a‖) * ‖holderCore u holder V c‖
  rw [hid]
  exact BoundedHolderSpace.product_norm_le u a _

end LeanShared.SmoothHolderTestSpaces
