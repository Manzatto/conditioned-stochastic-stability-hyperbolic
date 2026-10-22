module
public import LeanShared.Dynamics.WeightedOrbitTransientEnds
public import LeanShared.Geometry.DiffeomorphismIterates
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The literal whole orbit integral reduces to the surviving middle orbit
integral with a fixed prefix/suffix cost and a reference pushforward bound. -/
public noncomputable section
namespace LeanShared.WeightedOrbitSurvivorIntegral
open Set MeasureTheory
open scoped ENNReal BigOperators

@[expose] def survivors {X : Type*} (T : X → X) (K : Set X) (n : ℕ) : Set X :=
  {y | ∀ j ≤ n, T^[j] y ∈ K}

theorem survivors_isClosed {X : Type*} [TopologicalSpace X]
    (T : X → X) (continuous : Continuous T) (K : Set X) (closed : IsClosed K) (n : ℕ) :
    IsClosed (survivors T K n) := by
  change IsClosed {y | ∀ j, ∀ (_ : j ≤ n), T^[j] y ∈ K}
  simp only [ofPred_forall]
  exact isClosed_iInter fun j => isClosed_iInter fun _ => closed.preimage (continuous.iterate j)

theorem integral_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (σ : Measure X) (g : X → ℝ) (continuous : Continuous g)
    (nonnegative : ∀ x, 0 ≤ g x) (G : ℝ) (positiveG : 0 ≤ G) (bounded : ∀ x, g x ≤ G)
    (K : Set X) (closed : IsClosed K) (supported : Function.support g ⊆ K)
    (L n : ℕ) (C : ℝ≥0∞) (mapBound : σ.map (T^L) ≤ C • σ) :
    (∫⁻ y, ENNReal.ofReal (∏ j ∈ Finset.range (n+2*L+1), g ((T : X → X)^[j] y)) ∂σ) ≤
      ENNReal.ofReal (G^(2*L+1)) * C *
        ∫⁻ y in (T^L) '' survivors T K (n+2*L),
          ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : X → X)^[j] y)) ∂σ := by
  classical
  let S := survivors T K (n+2*L)
  let H := T^L
  let F := fun y => ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : X → X)^[j] y))
  let Q := (H '' S).indicator F
  have closedS : IsClosed S := survivors_isClosed T T.continuous K closed _
  have measurableImage : MeasurableSet (H '' S) := (H.isClosedMap S closedS).measurableSet
  have measurableF : Measurable F :=
    ((continuous_finsetProd _ (fun j _ => continuous.comp (T.continuous.iterate j))).measurable).ennreal_ofReal
  have measurableQ : Measurable Q := measurableF.indicator measurableImage
  have pointwise (y : X) :
      ENNReal.ofReal (∏ j ∈ Finset.range (n+2*L+1), g ((T : X → X)^[j] y)) ≤
      ENNReal.ofReal (G^(2*L+1)) * Q (H y) := by
    by_cases inside : y ∈ S
    · have image : H y ∈ H '' S := mem_image_of_mem H inside
      rw [show Q (H y) = F (H y) from indicator_of_mem image F]
      have bound := ENNReal.ofReal_le_ofReal
        (WeightedOrbitTransientEnds.product_bound T g nonnegative G positiveG bounded L n y)
      rw [ENNReal.ofReal_mul (pow_nonneg positiveG _)] at bound
      simpa only [F,H,DiffeomorphismIterates.coe_pow] using bound
    · have failure : ∃ j ≤ n+2*L, g ((T : X → X)^[j] y) = 0 := by
        have outside : ¬ ∀ j ≤ n+2*L, (T : X → X)^[j] y ∈ K := inside
        push Not at outside
        obtain ⟨j,hj,notin⟩ := outside
        refine ⟨j,hj,?_⟩
        by_contra nonzero
        exact notin (supported nonzero)
      obtain ⟨j,hj,zero⟩ := failure
      have productZero : (∏ k ∈ Finset.range (n+2*L+1), g ((T : X → X)^[k] y)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr (by omega)) zero
      rw [productZero, ENNReal.ofReal_zero]
      exact bot_le
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (G^(2*L+1)) * Q (H y) ∂σ := lintegral_mono pointwise
    _ = ENNReal.ofReal (G^(2*L+1)) * ∫⁻ y, Q (H y) ∂σ :=
      lintegral_const_mul _ (measurableQ.comp H.continuous.measurable)
    _ = ENNReal.ofReal (G^(2*L+1)) * ∫⁻ y, Q y ∂σ.map H := by
      rw [lintegral_map' measurableQ.aemeasurable H.continuous.measurable.aemeasurable]
    _ ≤ ENNReal.ofReal (G^(2*L+1)) * ∫⁻ y, Q y ∂(C • σ) :=
      mul_le_mul le_rfl (lintegral_mono' mapBound le_rfl) bot_le bot_le
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, lintegral_indicator measurableImage]; exact (mul_assoc _ _ _).symm

end LeanShared.WeightedOrbitSurvivorIntegral
