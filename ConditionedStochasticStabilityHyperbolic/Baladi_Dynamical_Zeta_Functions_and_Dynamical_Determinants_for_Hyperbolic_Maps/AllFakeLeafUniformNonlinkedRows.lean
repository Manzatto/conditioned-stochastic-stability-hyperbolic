module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafGlobalNonlinkedRows

/-! The actual nonlinked constants are selected before every homeomorphism
and amplitude with the displayed uniform primitive bounds. The parameter
space is the whole bounded class, so constants cannot depend on a chosen
noise control or chart configuration. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared ConeDyadicSymbols BTLinkedDyadicWeights
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {I ι κ : Type*} [Finite I] [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem exists_uniform_nonlinked_block_bound
    (ambientBasis : OrthonormalBasis κ ℝ E)
    (planes : I → Submodule ℝ E) (plus : I → Set E)
    (cone : ∀ i, ConeData (planes i) (plus i))
    (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
    (basis : ∀ i, OrthonormalBasis ι ℝ (planes i)) (i : I)
    {Dp Dm Cm narrow : Set E} (sourceCone : ConeData (planes i) Dp)
    {α D L G₀ G₁ K upper lower : ℝ}
    (hα : 0 < α) (hD : 0 ≤ D) (hL : 0 ≤ L) (hG₀ : 0 ≤ G₀) (hG₁ : 0 ≤ G₁) (hK : 0 ≤ K)
    (closedNarrow : IsClosed narrow) (margin : ∀ v ∈ narrow, v ≠ 0 → v ∈ interior Dm)
    (sourceScale : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ plus i, c • v ∈ plus i)
    (targetScale : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ Dm, c • v ∈ Dm)
    (hu : 0 < upper) (hl : 0 < lower)
    (outputRadial inputRadial : RadialCutoff) (outputAngle : AngularCutoff Dp Dm)
    (inputCutoffs : ConstructedEnlargedConeSymbols.Cutoffs (plus i) Cm)
    {L₀ : Set E} (compactL₀ : IsCompact L₀)
    {S : Set E} (compactS : IsCompact S) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (t : Bool → ℝ) (tBound : ∀ sign, t sign ≤ b) :
    ∃ N : ℕ, ∃ C : ℝ≥0,
      ∀ (H : E ≃ₜ E), ContDiff ℝ 1 H → ContDiff ℝ 1 H.symm →
      (∀ x, ‖fderiv ℝ H x‖ ≤ D) →
      (∀ x y, ‖fderiv ℝ H x-fderiv ℝ H y‖ ≤ L*dist x y^α) →
      (∀ x, ‖fderiv ℝ H.symm x‖ ≤ K) →
      (∀ x v, v ≠ 0 → v ∉ interior (plus i) → (fderiv ℝ H x).adjoint v ∈ narrow) →
      (∀ x v, (fderiv ℝ H x).adjoint v ∉ narrow → ‖(fderiv ℝ H x).adjoint v‖ ≤ upper*‖v‖) →
      (∀ x v, v ∉ interior (plus i) → lower*‖v‖ ≤ ‖(fderiv ℝ H x).adjoint v‖) →
      ∀ g : E →ᵇ ℂ, tsupport (fun w => g w) ⊆ L₀ →
      (∀ w, ‖g w‖ ≤ G₀) → (∀ x y, ‖g x-g y‖ ≤ G₁*dist x y^α) →
      (∀ Γ : Index (planes i) Dp, ∃ image : Index (planes i) (plus i), image.val = H '' Γ.val) →
      ∀ (j k : ℕ × Bool), N < max j.1 k.1 →
      ¬ linked (plusThreshold upper) (minusThreshold lower) j k →
      ∀ f : SchwartzJetSpace.supportedCore S, ∀ Γ : Index (planes i) Dp,
      (∫⁻ x, ‖∫ w, FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w) *
        g w * ConeFourierBlocks.block (symbols inputRadial inputCutoffs.original k) f.val (H w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)^(-α*(max j.1 k.1 : ℕ))) *
          (ENNReal.ofReal ((2 : ℝ)^(-(t k.2 * k.1))) *
            ENNReal.ofReal ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
              inputRadial inputCutoffs.original compactS hb hb1 t tBound i f‖) := by
  let accepted (z : (E ≃ₜ E) × (E →ᵇ ℂ)) : Prop :=
    ContDiff ℝ 1 z.1 ∧ ContDiff ℝ 1 z.1.symm ∧
    (∀ x, ‖fderiv ℝ z.1 x‖ ≤ D) ∧
    (∀ x y, ‖fderiv ℝ z.1 x-fderiv ℝ z.1 y‖ ≤ L*dist x y^α) ∧
    (∀ x, ‖fderiv ℝ z.1.symm x‖ ≤ K) ∧
    (∀ x v, v ≠ 0 → v ∉ interior (plus i) → (fderiv ℝ z.1 x).adjoint v ∈ narrow) ∧
    (∀ x v, (fderiv ℝ z.1 x).adjoint v ∉ narrow → ‖(fderiv ℝ z.1 x).adjoint v‖ ≤ upper*‖v‖) ∧
    (∀ x v, v ∉ interior (plus i) → lower*‖v‖ ≤ ‖(fderiv ℝ z.1 x).adjoint v‖) ∧
    tsupport (fun w => z.2 w) ⊆ L₀ ∧
    (∀ w, ‖z.2 w‖ ≤ G₀) ∧ (∀ x y, ‖z.2 x-z.2 y‖ ≤ G₁*dist x y^α) ∧
    ∀ Γ : Index (planes i) Dp, ∃ image : Index (planes i) (plus i), image.val = z.1 '' Γ.val
  let P := {z : (E ≃ₜ E) × (E →ᵇ ℂ) // accepted z}
  obtain ⟨N,C,rows⟩ := exists_global_nonlinked_block_bound ambientBasis planes plus cone coordinates basis i
    sourceCone (fun p : P => p.val.1) (fun p => p.property.1) (fun p => p.property.2.1)
    hα hD hL hG₀ hG₁ hK
    (fun p => p.property.2.2.1) (fun p => p.property.2.2.2.1) (fun p => p.property.2.2.2.2.1)
    closedNarrow margin sourceScale targetScale (fun p => p.property.2.2.2.2.2.1) hu hl
    (fun p => p.property.2.2.2.2.2.2.1) (fun p => p.property.2.2.2.2.2.2.2.1)
    outputRadial inputRadial outputAngle inputCutoffs (fun p => p.val.2) compactL₀
    (fun p => p.property.2.2.2.2.2.2.2.2.1) (fun p => p.property.2.2.2.2.2.2.2.2.2.1)
    (fun p => p.property.2.2.2.2.2.2.2.2.2.2.1) (fun p => p.property.2.2.2.2.2.2.2.2.2.2.2)
    compactS hb hb1 t tBound
  refine ⟨N,C,?_⟩
  intro H smooth inverseSmooth value holder inverse action upperBound lowerBound g supported gvalue gholder images
  let p : P := ⟨(H,g),smooth,inverseSmooth,value,holder,inverse,action,upperBound,lowerBound,
    supported,gvalue,gholder,images⟩
  exact rows p

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
