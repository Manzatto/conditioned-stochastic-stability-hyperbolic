module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeInputBounds
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! A native chart slot whose actual transverse plane and cone equal the
canonical output geometry controls all canonical full fake leaves. The
physical norm remains the complete heterogeneous family norm. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
open LeanShared AllFakeLeafModel
variable {E I ι : Type*} [Finite I] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i))
  {minus Cp : Set E} (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff Cp minus)
  {K : Set E} (compact : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (t : Bool → ℝ) (margin : ∀ sign, t sign ≤ b)

set_option backward.isDefEq.respectTransparency false in
theorem canonical_input_leaf_bound (i : I) (P : Submodule ℝ E) (C : Set E)
    (planeSame : planes i = P) (plusSame : plus i = C)
    (f : SchwartzJetSpace.supportedCore K) (j : ℕ × Bool) (Γ : Index P C) :
    (∫⁻ x, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle j) f.val x‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume P volume Γ.val) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(t j.2 * j.1))) *
        ENNReal.ofReal ‖coreBlocks planes plus cone coordinates basis radial angle compact hb hb1 t margin i f‖ := by
  let native : Index (planes i) (plus i) := ⟨Γ.val, by
    rw [planeSame, plusSame]
    exact Γ.property⟩
  have bound := input_leaf_bound planes plus cone coordinates basis radial angle compact hb hb1 t margin i f j native
  have sameMeasure : EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val =
      EmbeddedSubmanifoldVolume.volume P volume Γ.val := by rw [planeSame]
  change (∫⁻ x, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle j) f.val x‖ₑ
    ∂EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val) ≤ _ at bound
  rw [sameMeasure] at bound
  exact bound

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
