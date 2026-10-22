module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalInputBounds
public import LeanShared.Analysis.DyadicPhysicalRowWeight
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! Apply a raw principal leaf operator estimate to the literal input
blocks, with their actual heterogeneous full fake-leaf norm. The exponent
is arbitrary: the same theorem gives the strong principal row and the
weak finite-square row, with no separate finite-square hypothesis. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal
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

theorem weighted_principal_block_row (i : I) (P : Submodule ℝ E) (C : Set E)
    (planeSame : planes i = P) (plusSame : plus i = C)
    (f : SchwartzJetSpace.supportedCore K) (k : ℕ × Bool)
    (A cost : ℝ≥0) (row : ℝ≥0∞) (outputExponent : ℝ)
    (principal : ∀ B : ℝ≥0∞,
      (∀ Δ : Index P C,
        (∫⁻ x, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle k) f.val x‖ₑ
          ∂EmbeddedSubmanifoldVolume.volume P volume Δ.val) ≤ B) →
      row ≤ (A : ℝ≥0∞) * ((cost : ℝ≥0∞) * B)) :
    ENNReal.ofReal ((2 : ℝ)^outputExponent) * row ≤
      ENNReal.ofReal (((A * cost : ℝ≥0) : ℝ) *
        (2 : ℝ)^(outputExponent-t k.2*k.1) *
        ‖coreBlocks planes plus cone coordinates basis radial angle compact hb hb1 t margin i f‖) := by
  apply DyadicPhysicalRowWeight.principal (A * cost) outputExponent (t k.2*k.1)
    ‖coreBlocks planes plus cone coordinates basis radial angle compact hb hb1 t margin i f‖
  have raw := principal
    (ENNReal.ofReal ((2 : ℝ)^(-(t k.2*k.1))) *
      ENNReal.ofReal ‖coreBlocks planes plus cone coordinates basis radial angle compact hb hb1 t margin i f‖)
    (fun Δ => canonical_input_leaf_bound planes plus cone coordinates basis radial angle
      compact hb hb1 t margin i P C planeSame plusSame f k Δ)
  simpa only [ENNReal.coe_mul, mul_assoc] using raw

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
