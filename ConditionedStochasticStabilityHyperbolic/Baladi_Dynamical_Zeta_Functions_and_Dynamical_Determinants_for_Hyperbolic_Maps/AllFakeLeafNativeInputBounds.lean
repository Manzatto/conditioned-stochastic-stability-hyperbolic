module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHolderCoreBounds
public import LeanShared.Analysis.CompactHolderPhysicalBlockBounds
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! The actual heterogeneous full fake-leaf input norm controls every
literal physical input block in canonical induced Euclidean volume. Neither
a leaf-integral bound nor a norm comparison constant is an input. -/
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

@[expose] def coreBlocks (i : I) := SchwartzAmbientBlocks.coreMap
  (volume : Measure (EuclideanSpace ℝ ι))
  (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
  (leaves planes plus cone coordinates basis i) K (ConeDyadicSymbols.symbols radial angle) t
  (bounded planes plus cone coordinates basis radial angle compact hb hb1 t margin i)

set_option backward.isDefEq.respectTransparency false in
theorem input_leaf_bound (i : I) (f : SchwartzJetSpace.supportedCore K)
    (j : ℕ × Bool) (Γ : Index (planes i) (plus i)) :
    (∫⁻ x, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle j) f.val x‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(t j.2 * j.1))) *
        ENNReal.ofReal ‖coreBlocks planes plus cone coordinates basis radial angle compact hb hb1 t margin i f‖ := by
  obtain ⟨a, same⟩ := Heterogeneous.evaluation_surjective planes plus i Γ
  change a i = Γ at same
  have bound := CompactHolderPhysicalBlocks.leaf_bound
    (volume : Measure (EuclideanSpace ℝ ι))
    (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
    (leaves planes plus cone coordinates basis i) radial angle compact hb hb1 t margin
    (CompactSchwartzHolderCore.core compact hb hb1 f) j a
  rw [CompactHolderPhysicalBlocks.realize_core] at bound
  simp_rw [CompactSchwartzHolderCore.physical_core, ← ConeFourierBlocks.block_apply] at bound
  have volumeMap : (volume : Measure (EuclideanSpace ℝ ι)).map (coordinates i) = volume :=
    (coordinates i).measurePreserving.map_eq
  have measureEq : (leaves planes plus cone coordinates basis i a).measure volume =
      EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val := by
    rw [leaves, Heterogeneous.leaves_measure, volumeMap, same]
    rfl
  rw [measureEq] at bound
  exact bound

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
