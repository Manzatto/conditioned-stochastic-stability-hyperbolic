module
public import LeanShared.Analysis.ProductRateConeBounds
public import LeanShared.Analysis.ProductConeWordBounds
public import LeanShared.Analysis.TriangularAdjointRadialBounds

/-! Actual products of near-hyperbolic matrices have constructed graph
factorizations and the closed-cone radial alternatives. Conjugations cancel
inside the word; the constants four occur only at its two endpoints. -/
@[expose] public noncomputable section
open Function Set
namespace LeanShared.ProductRateWordRadialBounds

def wordEquiv {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    List (Z ≃L[ℝ] Z) → Z ≃L[ℝ] Z
  | [] => ContinuousLinearEquiv.refl ℝ Z
  | B::tail => B.trans (wordEquiv tail)

theorem conjugate_word {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (e : Z ≃L[ℝ] W) (blocks : List (Z ≃L[ℝ] Z)) :
    wordEquiv (blocks.map (fun B => e.symm.trans (B.trans e))) =
      e.symm.trans ((wordEquiv blocks).trans e) := by
  induction blocks with
  | nil =>
    apply DFunLike.ext
    intro z
    exact (e.apply_symm_apply z).symm
  | cons B tail ih =>
    apply DFunLike.ext
    intro z
    simp only [List.map_cons, wordEquiv, ih, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply]

section Normed
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem word_coe (blocks : List ((X×Y) ≃L[ℝ] (X×Y))) :
    (wordEquiv blocks).toContinuousLinearMap =
      ProductConeWordBounds.word (blocks.map (fun B => B.toContinuousLinearMap)) := by
  apply ContinuousLinearMap.ext
  intro z
  induction blocks generalizing z with
  | nil => rfl
  | cons B tail ih => exact ih (B z)

theorem forward_narrow (blocks : List ((X×Y) ≃L[ℝ] (X×Y))) {c : ℝ}
    (step : ∀ B ∈ blocks, ∀ z, ‖z.2‖ ≤ c*‖z.1‖ → ‖(B z).2‖ ≤ c*‖(B z).1‖)
    (z : X×Y) (input : ‖z.2‖ ≤ c*‖z.1‖) :
    ‖(wordEquiv blocks z).2‖ ≤ c*‖(wordEquiv blocks z).1‖ := by
  induction blocks generalizing z with
  | nil => exact input
  | cons B tail ih =>
    exact ih (fun C hC => step C (List.mem_cons_of_mem B hC)) (B z)
      (step B List.mem_cons_self z input)

theorem backward_narrow (blocks : List ((X×Y) ≃L[ℝ] (X×Y))) {c : ℝ}
    (step : ∀ B ∈ blocks, ∀ z, ‖(B z).1‖ ≤ c*‖(B z).2‖ → ‖z.1‖ ≤ c*‖z.2‖)
    (z : X×Y) (target : ‖(wordEquiv blocks z).1‖ ≤ c*‖(wordEquiv blocks z).2‖) :
    ‖z.1‖ ≤ c*‖z.2‖ := by
  induction blocks generalizing z with
  | nil => exact target
  | cons B tail ih =>
    exact step B List.mem_cons_self z
      (ih (fun C hC => step C (List.mem_cons_of_mem B hC)) (B z) target)

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

theorem factorization_of_steps (blocks : List ((X×Y) ≃L[ℝ] (X×Y)))
    {c a b : ℝ} (nonnegativeC : 0 ≤ c) (nonnegativeA : 0 ≤ a) (positiveB : 0 < b)
    (backward : ∀ B ∈ blocks, ∀ z, ‖(B z).1‖ ≤ c*‖(B z).2‖ → ‖z.1‖ ≤ c*‖z.2‖)
    (forward : ∀ B ∈ blocks, ∀ z, ‖z.2‖ ≤ c*‖z.1‖ → ‖(B z).2‖ ≤ c*‖(B z).1‖)
    (stable : ∀ B ∈ blocks, ∀ z, ‖(B z).1‖ ≤ ‖(B z).2‖ →
      ‖z.1‖ ≤ ‖z.2‖ ∧ ‖B z‖ ≤ a*‖z‖)
    (unstable : ∀ B ∈ blocks, ∀ z, ‖z.2‖ ≤ ‖z.1‖ →
      ‖(B z).2‖ ≤ ‖(B z).1‖ ∧ ‖z‖ ≤ b*‖B z‖) :
    ∃ J : X ≃L[ℝ] X, ∃ K : Y →L[ℝ] X, ∃ L : X →L[ℝ] Y, ∃ S₀ : Y ≃L[ℝ] Y,
      (∀ u s, wordEquiv blocks (u,s) = (J (u-K s), L (J (u-K s))+S₀ s)) ∧
      ‖K‖ ≤ c ∧ ‖L‖ ≤ c ∧ ‖J.symm.toContinuousLinearMap‖ ≤ b^blocks.length ∧
        ‖S₀.toContinuousLinearMap‖ ≤ a^blocks.length := by
  let linearBlocks := blocks.map (fun B => B.toContinuousLinearMap)
  have stableLinear : ∀ B ∈ linearBlocks, ∀ z, ‖(B z).1‖ ≤ ‖(B z).2‖ →
      ‖z.1‖ ≤ ‖z.2‖ ∧ ‖B z‖ ≤ a*‖z‖ := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
    exact stable C hC
  have unstableLinear : ∀ B ∈ linearBlocks, ∀ z, ‖z.2‖ ≤ ‖z.1‖ →
      ‖(B z).2‖ ≤ ‖(B z).1‖ ∧ ‖z‖ ≤ b*‖B z‖ := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
    exact unstable C hC
  have expansion (u : X) : (b^blocks.length)⁻¹*‖u‖ ≤ ‖(wordEquiv blocks (u,0)).1‖ := by
    have facts := ProductConeWordBounds.inverse_unstable b positiveB.le linearBlocks unstableLinear
      (u,0) (by simp)
    rw [← word_coe blocks] at facts
    simp only [ContinuousLinearEquiv.coe_coe] at facts
    have normInput : ‖(u,(0 : Y))‖ = ‖u‖ := by simp
    have normOutput : ‖wordEquiv blocks (u,0)‖ = ‖(wordEquiv blocks (u,0)).1‖ := by
      rw [Prod.norm_def, max_eq_left facts.1]
    have bound : ‖u‖ ≤ b^blocks.length*‖(wordEquiv blocks (u,0)).1‖ := by
      simpa only [normInput, normOutput, linearBlocks, List.length_map] using facts.2
    have divide : ‖u‖/(b^blocks.length) ≤ ‖(wordEquiv blocks (u,0)).1‖ :=
      (div_le_iff₀ (pow_pos positiveB _)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using divide
  have contraction (v : X×Y) (target : (wordEquiv blocks v).1 = 0) :
      ‖(wordEquiv blocks v).2‖ ≤ a^blocks.length*‖v.2‖ := by
    have wide : ‖(wordEquiv blocks v).1‖ ≤ ‖(wordEquiv blocks v).2‖ := by rw [target, norm_zero]; positivity
    have linearTarget : ‖(ProductConeWordBounds.word linearBlocks v).1‖ ≤
        ‖(ProductConeWordBounds.word linearBlocks v).2‖ := by rw [← word_coe blocks]; exact wide
    have facts := ProductConeWordBounds.stable a nonnegativeA linearBlocks stableLinear v linearTarget
    rw [← word_coe blocks] at facts
    simp only [ContinuousLinearEquiv.coe_coe] at facts
    have normOutput : ‖wordEquiv blocks v‖ = ‖(wordEquiv blocks v).2‖ := by
      rw [Prod.norm_def, max_eq_right wide]
    have normInput : ‖v‖ = ‖v.2‖ := by rw [Prod.norm_def, max_eq_right facts.1]
    simpa only [normInput, normOutput, linearBlocks, List.length_map] using facts.2
  obtain ⟨J, K, L, S₀, _Jactual, _stableGraph, factorization, normK, normL, normJ, normS⟩ :=
    ProductConeBlockFactorization.exists_factorization (wordEquiv blocks) nonnegativeC
      (inv_pos.mpr (pow_pos positiveB _)) (pow_nonneg nonnegativeA _)
      (fun u => forward_narrow blocks forward (u,0) (by simp; positivity))
      (fun v hv => backward_narrow blocks backward v (by rw [hv, norm_zero]; positivity))
      expansion contraction
  exact ⟨J, K, L, S₀, factorization, normK, normL, by simpa only [inv_inv] using normJ, normS⟩

end Normed

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
/-- The real near-diagonal matrices themselves produce the factorization,
its exponential bounds, and the closed narrow-cone radial alternatives. -/
theorem exists_uniform_radial_bounds {q : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) :
    ∃ δ : ℝ, 0 < δ ∧ q+δ < 1 ∧ 1 < 1/q-δ ∧
      ∀ blocks : List ((X×Y) ≃L[ℝ] (X×Y)),
      (∀ B ∈ blocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
        ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
          ‖B.toContinuousLinearMap-U.toContinuousLinearMap.prodMap S‖ ≤ δ) →
      ∃ J : X ≃L[ℝ] X, ∃ K : Y →L[ℝ] X, ∃ L : X →L[ℝ] Y, ∃ S₀ : Y ≃L[ℝ] Y,
        (∀ u s, wordEquiv blocks (u,s) = (J (u-K s), L (J (u-K s))+S₀ s)) ∧
        ‖K‖ ≤ 1/8 ∧ ‖L‖ ≤ 1/8 ∧
        ‖J.symm.toContinuousLinearMap‖ ≤ ((1/q-δ)⁻¹)^blocks.length ∧
        ‖S₀.toContinuousLinearMap‖ ≤ (q+δ)^blocks.length ∧
        (∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
          (OrthogonalProductCoordinates.transport dimension (wordEquiv blocks).toContinuousLinearMap).adjoint ξ ∉
            ProjectionConeTransversality.cone (OrthogonalProductCoordinates.secondProjection dimension) β →
          ‖(OrthogonalProductCoordinates.transport dimension (wordEquiv blocks).toContinuousLinearMap).adjoint ξ‖ ≤
            4*(q+δ)^blocks.length*‖ξ‖) ∧
        (∀ ξ : E, ξ ∉ interior (ProjectionConeTransversality.cone
            (OrthogonalProductCoordinates.firstProjection dimension) (1/2)) →
          (4*((1/q-δ)⁻¹)^blocks.length)⁻¹*‖ξ‖ ≤
            ‖(OrthogonalProductCoordinates.transport dimension (wordEquiv blocks).toContinuousLinearMap).adjoint ξ‖) ∧
        ∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
          (OrthogonalProductCoordinates.transport dimension (wordEquiv blocks).toContinuousLinearMap).adjoint ξ ∈
              ProjectionConeTransversality.cone (OrthogonalProductCoordinates.secondProjection dimension) β ∨
            ‖(OrthogonalProductCoordinates.transport dimension (wordEquiv blocks).toContinuousLinearMap).adjoint ξ‖ ≤
              4*(q+δ)^blocks.length*‖ξ‖ := by
  obtain ⟨δ, positiveδ, stableRate, unstableRate, budget⟩ :=
    ProductRateConeBounds.exists_budget (X := X) (Y := Y) positiveQ contractingQ
      (by norm_num : (0:ℝ) < 1/8) (by norm_num : (1/8:ℝ) ≤ 1)
  refine ⟨δ, positiveδ, stableRate, unstableRate, fun blocks near => ?_⟩
  have facts (B : (X×Y) ≃L[ℝ] (X×Y)) (hB : B ∈ blocks) :
      (∀ z, ‖(B z).1‖ ≤ (1/8)*‖(B z).2‖ → ‖z.1‖ ≤ (1/8)*‖z.2‖) ∧
      (∀ z, ‖z.2‖ ≤ (1/8)*‖z.1‖ → ‖(B z).2‖ ≤ (1/8)*‖(B z).1‖) ∧
      (∀ z, ‖(B z).1‖ ≤ ‖(B z).2‖ → ‖z.1‖ ≤ ‖z.2‖ ∧ ‖B z‖ ≤ (q+δ)*‖z‖) ∧
      (∀ z, ‖z.2‖ ≤ ‖z.1‖ → ‖(B z).2‖ ≤ ‖(B z).1‖ ∧ ‖z‖ ≤ (1/q-δ)⁻¹*‖B z‖) := by
    obtain ⟨U, S, stable, unstable, close⟩ := near B hB
    exact budget U S B.toContinuousLinearMap stable unstable close
  have inversePositive : 0 < (1/q-δ)⁻¹ := inv_pos.mpr (by linarith)
  obtain ⟨J, K, L, S₀, factorization, normK, normL, normJ, normS⟩ :=
    factorization_of_steps blocks (by norm_num : (0:ℝ) ≤ 1/8)
      (by positivity : 0 ≤ q+δ) inversePositive
      (fun B hB => (facts B hB).1) (fun B hB => (facts B hB).2.1)
      (fun B hB => (facts B hB).2.2.1) (fun B hB => (facts B hB).2.2.2)
  refine ⟨J, K, L, S₀, factorization, normK, normL, normJ, normS, ?_, ?_, ?_⟩
  · intro β hβ ξ outside
    exact TriangularAdjointRadialBounds.upper dimension (wordEquiv blocks).toContinuousLinearMap
      J.toContinuousLinearMap K L S₀.toContinuousLinearMap factorization
      (pow_nonneg (by positivity : 0 ≤ q+δ) _) hβ normK normS ξ outside
  · intro ξ outside
    exact TriangularAdjointRadialBounds.lower dimension (wordEquiv blocks).toContinuousLinearMap
      J K L S₀.toContinuousLinearMap factorization (pow_pos inversePositive _) normL normJ ξ outside
  · intro β hβ ξ
    exact TriangularAdjointRadialBounds.closed_narrow_or_upper dimension (wordEquiv blocks).toContinuousLinearMap
      J.toContinuousLinearMap K L S₀.toContinuousLinearMap factorization
      (pow_nonneg (by positivity : 0 ≤ q+δ) _) hβ normK normS ξ

end LeanShared.ProductRateWordRadialBounds
