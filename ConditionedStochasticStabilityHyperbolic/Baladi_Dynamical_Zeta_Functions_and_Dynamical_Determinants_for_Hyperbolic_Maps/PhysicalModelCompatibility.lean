module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModelCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedOperatorIdentity

/-! Shared literal finite-regular functions derive compatibility of two
actual analytic exponent models. No anisotropic operator intertwining or
projector compatibility is a source assumption. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelCompatibility
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

private theorem dense_comp_eq {C R A B : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup R] [NormedSpace ℂ R]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (q : C →ₗ[ℂ] R) (hdense : DenseRange q)
    (f : R →L[ℂ] A) (g : R →L[ℂ] B) (i : A →L[ℂ] B)
    (hc : ∀ c, i (f (q c)) = g (q c)) : i.comp f = g := by
  apply ContinuousLinearMap.ext
  intro x
  exact hdense.induction_on (p := fun x => i (f x) = g x) x
    (isClosed_eq (i.continuous.comp f.continuous) g.continuous) hc

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m n : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


variable (hreg : m.regularCore = n.regularCore)
  (hview : m.view = n.view) (hmaps : m.maps = n.maps) (hweight : m.weight = n.weight)

include hview hmaps hweight in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem regular_action_eq (a : Ω) (c : PhysicalManifoldModel.Core (E := E) V) :
    regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.maps m.weight m.coreRegular a c =
    regularAction (SmoothSupportedManifoldCore.functions V) Reg n.view n.view_injective
      n.maps n.weight n.coreRegular a c := by
  apply n.view_injective
  funext x
  calc
    n.view (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.maps m.weight m.coreRegular a c) x =
      m.view (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c) x :=
      congrArg (fun v => v (regularAction (SmoothSupportedManifoldCore.functions V) Reg
        m.view m.view_injective m.maps m.weight m.coreRegular a c) x) hview.symm
    _ = (m.weight x : ℂ) * SmoothSupportedManifoldCore.functions V c (m.maps a x) :=
      regularAction_apply (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c x
    _ = (n.weight x : ℂ) * SmoothSupportedManifoldCore.functions V c (n.maps a x) :=
      congrArg₂ (fun (r : ℝ) (z : ℂ) => (r : ℂ) * z)
        (congrArg (fun w : M → ℝ => w x) hweight)
        (congrArg (fun maps : Ω → M → M => SmoothSupportedManifoldCore.functions V c (maps a x)) hmaps)
    _ = n.view (regularAction (SmoothSupportedManifoldCore.functions V) Reg n.view n.view_injective
      n.maps n.weight n.coreRegular a c) x := (regularAction_apply (SmoothSupportedManifoldCore.functions V) Reg n.view n.view_injective
        n.maps n.weight n.coreRegular a c x).symm

include hreg in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
set_option maxHeartbeats 1600000 in
private theorem realization_intertwining (i : m.StrongSpace →L[ℂ] n.StrongSpace)
    (hcore : ∀ c, i (coreLift m.qa c) = coreLift n.qa c) :
    i.comp m.realize = n.realize := by
  apply dense_comp_eq m.regularCore m.regularCore_dense
  intro c
  have hm := m.realize_core c
  have hn := n.realize_core c
  have hr := congrArg (fun q : PhysicalManifoldModel.Core (E := E) V →ₗ[ℂ] Reg => q c) hreg
  exact (congrArg i hm).trans ((hcore c).trans
    (hn.symm.trans (congrArg n.realize hr).symm))

include hreg hview hmaps hweight in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
set_option maxHeartbeats 1600000 in
private theorem generator_intertwining (i : m.StrongSpace →L[ℂ] n.StrongSpace)
    (hcore : ∀ c, i (coreLift m.qa c) = coreLift n.qa c)
    (hm : ∀ a c, m.generator a (coreLift m.qa c) = m.realize
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c))
    (hn : ∀ a c, n.generator a (coreLift n.qa c) = n.realize
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg n.view n.view_injective
        n.maps n.weight n.coreRegular a c)) (a : Ω) :
    i.comp (m.generator a) = (n.generator a).comp i := by
  have hir := realization_intertwining m n hreg i hcore
  apply ContinuousLinearMap.ext
  intro f
  apply (coreLift_dense m.qa).induction_on
    (p := fun f => i (m.generator a f) = n.generator a (i f)) f
    (isClosed_eq (i.continuous.comp (m.generator a).continuous)
      ((n.generator a).continuous.comp i.continuous))
  intro c
  change i (m.generator a (coreLift m.qa c)) = n.generator a (i (coreLift m.qa c))
  calc
    _ = i (m.realize (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      m.view m.view_injective m.maps m.weight m.coreRegular a c)) := congrArg i (hm a c)
    _ = n.realize (regularAction (SmoothSupportedManifoldCore.functions V) Reg
      n.view n.view_injective n.maps n.weight n.coreRegular a c) := by
      have hh := congrArg (fun L : Reg →L[ℂ] n.StrongSpace => L
        (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
          m.maps m.weight m.coreRegular a c)) hir
      exact hh.trans (congrArg n.realize (regular_action_eq m n hview hmaps hweight a c))
    _ = n.generator a (coreLift n.qa c) := (hn a c).symm
    _ = _ := congrArg (n.generator a) (hcore c).symm

structure CompatibleOperators {X Y R N : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup R] [NormedSpace ℂ R]
    (rx : R →L[ℂ] X) (ry : R →L[ℂ] Y)
    (Px : N → X →L[ℂ] X) (Py : N → Y →L[ℂ] Y) (i : X →L[ℂ] Y) : Type where
  realization : i.comp rx = ry
  generator : ∀ a, i.comp (Px a) = (Py a).comp i

include hreg hview hmaps hweight in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
def compatibleOperators (i : m.StrongSpace →L[ℂ] n.StrongSpace)
    (hcore : ∀ c, i (coreLift m.qa c) = coreLift n.qa c)
    (hm : ∀ a c, m.generator a (coreLift m.qa c) = m.realize
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c))
    (hn : ∀ a c, n.generator a (coreLift n.qa c) = n.realize
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg n.view n.view_injective
        n.maps n.weight n.coreRegular a c)) :
    CompatibleOperators m.realize n.realize m.generator n.generator i := {
  realization := realization_intertwining m n hreg i hcore
  generator := generator_intertwining m n hreg hview hmaps hweight i hcore hm hn }

end ConditionedStochasticStabilityHyperbolic.PhysicalModelCompatibility
