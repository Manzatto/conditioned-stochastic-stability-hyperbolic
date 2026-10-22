module
public import LeanShared.Analysis.SchwartzAmbientRealization

/-! The actual ambient leaf-supremum realization obeys every proved radial
envelope, independently of its internally chosen Schwartz decay constant. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.SchwartzAmbientRealization
variable {E U A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

theorem norm_le_of_envelope (f : 𝓢(E,ℂ)) {r C : ℝ}
    (hr : (Module.finrank ℝ U : ℝ)<r) (hC : 0≤C)
    (envelope : ∀ x, ‖f x‖≤C*GraphLeafNorm.radialWeight r x) :
    ‖realization μ hJ leaves f‖ ≤ C*J*∫u,GraphLeafNorm.radialWeight r u ∂μ := by
  let z := GraphLeafNorm.ambientOfDecayingFunction μ hJ hr f.continuous.measurable hC envelope
  have equal : realization μ hJ leaves f = GraphLeafNorm.restrictFamily μ leaves z := by
    apply lp.ext
    funext a
    apply Lp.ext
    have actual := realization_ae μ hJ leaves f a
    have alternate := MemLp.coeFn_toLp
      (memLp_one_iff_integrable.mpr
        (GraphLeafNorm.integrable_ambient μ hr f.continuous.measurable hC envelope (leaves a)))
    exact actual.trans alternate.symm
  rw [equal]
  calc
    _ ≤ ‖z‖ := by
      simpa only [one_mul] using
        (GraphLeafNorm.restrictFamily μ leaves).le_of_opNorm_le (GraphLeafNorm.restrictFamily_norm_le μ leaves) z
    _ = ‖GraphLeafNorm.ofDecayingFunction μ (hJ:=hJ) (hr:=hr)
        (hf:=f.continuous.measurable) (hA:=hC) (hdecay:=envelope)‖ :=
      GraphLeafNorm.norm_ambientOfDecayingFunction_eq_source μ hJ hr f.continuous.measurable hC envelope
    _ ≤ _ := GraphLeafNorm.norm_ofDecayingFunction_le μ hJ hr f.continuous.measurable hC envelope
end LeanShared.SchwartzAmbientRealization
