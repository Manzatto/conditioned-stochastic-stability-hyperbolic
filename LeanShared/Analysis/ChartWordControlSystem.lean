module

public import LeanShared.Analysis.ActualChartWordControls
public import LeanShared.Geometry.ActualChartWordFibers

/-! Pre-control data for actual finite manifold words. Ordinary fixed-word
composition bounds and deterministic cone separation are fields; the common
nearby-word controls predicate is produced. Closed moving survivor relations
and an open deterministic cone-valid collar prevent a global-chart assumption. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.ChartWordControlSystem
open CylinderPrincipalCoefficient MicrolocalBlockParameters ActualChartWordControls
variable {E M Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [TopologicalSpace Ω]

structure Data (F : Ω → M ≃ₜ M) (reference : Ω) (N : ℕ) where
  out : OpenPartialHomeomorph M E
  inp : OpenPartialHomeomorph M E
  θ : M → ℂ
  g : M → ℝ
  K : Set E
  L : Set E
  compact : IsCompact K
  R : Set ((Fin N → Ω) × E)
  Rback : Set ((Fin N → Ω) × E)
  closed : IsClosed R
  source : R ⊆ univ ×ˢ K
  valid : R ⊆ ActualChartWordFibers.valid out inp F N
  good : Set E
  good_open : IsOpen good
  reference_good : fiber K R (fun _ => reference) ⊆ good
  good_valid : good ⊆ ActualChartWordFields.domain out inp F (List.ofFn (fun _ : Fin N => reference))
  m : ℕ
  δ : ℝ
  order_positive : 0 < m
  fraction_nonnegative : 0 ≤ δ
  fraction_lt_one : δ < 1
  U : Set Ω
  U_open : IsOpen U
  reference_mem : reference ∈ U
  MF : ℝ
  MB : ℝ
  MG : ℝ
  σ : ℝ
  MF_nonnegative : 0 ≤ MF
  MB_nonnegative : 0 ≤ MB
  MG_nonnegative : 0 ≤ MG
  gap_positive : 0 < σ
  composition : ∀ word : Fin N → Ω, (∀ i, word i ∈ U) →
    LocalBounds (ActualChartWordFields.forward out inp F (List.ofFn word)) (fiber K R word) m δ MF ∧
    LocalBounds (ActualChartWordFields.backward out inp F (List.ofFn word)) (fiber L Rback word) m δ MB ∧
    LocalBounds (ActualChartWordControls.weight out F θ g (List.ofFn word)) (fiber K R word) (m - 1) δ MG
  derivative_continuous : ContinuousOn (MovingChartWordPhase.derivative out inp F N)
    (ActualChartWordFibers.valid out inp F N)
  nonlinked : E → E → ℝ → Prop
  frequency : ∀ ξ η Λ, nonlinked ξ η Λ → ‖η‖ ≤ 2 * Λ
  deterministic : ∀ x ∈ K, x ∈ good → ∀ ξ η Λ, nonlinked ξ η Λ → 0 ≤ Λ →
    σ * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
      (MovingChartWordPhase.derivative out inp F N ((fun _ => reference), x)) η‖

namespace Data
variable {F : Ω → M ≃ₜ M} {reference : Ω} {N : ℕ} (d : Data (E := E) F reference N)

def predicate (p : Parameters) (word : Fin N → Ω) : Prop :=
  Controls d.out d.inp F d.θ d.g d.K d.L d.R d.Rback d.m d.δ word d.nonlinked p

private theorem exists_good_neighborhood :
    ∃ U : Set (Fin N → Ω), IsOpen U ∧ (fun _ => reference) ∈ U ∧
      ∀ word ∈ U, ∀ x ∈ d.K, (word, x) ∈ d.R → x ∈ d.good := by
  have hsub : ({fun _ : Fin N => reference} : Set (Fin N → Ω)) ×ˢ d.K ⊆
      d.Rᶜ ∪ (univ ×ˢ d.good) := by
    rintro ⟨word, x⟩ ⟨hw, hx⟩
    have hw' : word = fun _ => reference := mem_singleton_iff.mp hw
    subst word
    by_cases hr : ((fun _ => reference), x) ∈ d.R
    · exact Or.inr ⟨mem_univ _, d.reference_good ⟨hx, hr⟩⟩
    · exact Or.inl hr
  obtain ⟨U, W, hU, _, href, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton d.compact (d.closed.isOpen_compl.union (isOpen_univ.prod d.good_open)) hsub
  refine ⟨U, hU, singleton_subset_iff.mp href, ?_⟩
  intro word hw x hx hr
  exact (hUW ⟨hw, hKW hx⟩).resolve_left (not_not.mpr hr) |>.2

/-- Actual common parameters are constructed from the pre-control source;
no arbitrary parameterControl neighborhood is assumed. -/
theorem exists_controls :
    ∃ p : Parameters, ∃ V : Set Ω, IsOpen V ∧ reference ∈ V ∧ V ⊆ d.U ∧
      ∀ word : Fin N → Ω, (∀ i, word i ∈ V) → d.predicate p word := by
  obtain ⟨U, hU, href, hgood⟩ := d.exists_good_neighborhood
  have hd : ContinuousOn (MovingChartWordPhase.derivative d.out d.inp F N)
      ((U ×ˢ univ) ∩ d.R) := d.derivative_continuous.mono (fun _ hz => d.valid hz.2)
  have hbase : ContinuousOn (fun z : (Fin N → Ω) × E =>
      MovingChartWordPhase.derivative d.out d.inp F N ((fun _ => reference), z.2))
      ((U ×ˢ univ) ∩ d.R) := by
    apply d.derivative_continuous.comp (continuous_const.prodMk continuous_snd).continuousOn
    intro z hz
    exact d.good_valid (hgood z.1 hz.1.1 z.2 (d.source hz.2).2 hz.2)
  obtain ⟨W, hW, hrefW, hphase⟩ := MovingChartWordPhase.exists_uniform_phase
    d.out d.inp F N reference d.K d.compact d.R d.closed U hU href hd hbase d.σ d.gap_positive
  obtain ⟨Wgood, hWgood, hrefWgood, hbox⟩ := RobustTwoNormBlock.exists_open_box_of_mem_nhds
    N reference U (hU.mem_nhds href)
  let p : Parameters := ⟨d.MF, d.MB, d.MG, d.σ / 2,
    d.MF_nonnegative, d.MB_nonnegative, d.MG_nonnegative, div_pos d.gap_positive (by norm_num)⟩
  refine ⟨p, (d.U ∩ W) ∩ Wgood, (d.U_open.inter hW).inter hWgood,
    ⟨⟨d.reference_mem, hrefW⟩, hrefWgood⟩, fun _ hz => hz.1.1, ?_⟩
  intro word hw
  have hwu : ∀ i, word i ∈ d.U := fun i => (hw i).1.1
  have hww : ∀ i, word i ∈ W := fun i => (hw i).1.2
  have hwgood := hbox word (fun i => (hw i).2)
  obtain ⟨hf, hb, hg⟩ := d.composition word hwu
  refine ⟨d.order_positive, d.fraction_nonnegative, d.fraction_lt_one, hf, hb, hg, ?_⟩
  intro x hx ξ η Λ hnl hΛ
  exact hphase word hww x hx.1 hx.2 ξ η Λ hΛ (d.frequency ξ η Λ hnl)
    (d.deterministic x hx.1 (hgood word hwgood x hx.1 hx.2) ξ η Λ hnl hΛ)

end Data
end LeanShared.ChartWordControlSystem
