import V10.ProjectionPlurisubharmonic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# Integration of actual nonnegative plurisuperharmonic potentials

Lower semicontinuity follows from Fatou's lemma. The normalized supermean
inequality on each complex line follows from Tonelli's theorem, with the
actual planar disk measure and its area factor. Joint measurability is an
explicit input; neither the desired supermean inequality of the integral
nor its semicontinuity is assumed.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace V10.PluriPotentialIntegral
open PluriPotentialSeries ProjectionPlurisubharmonic
set_option backward.isDefEq.respectTransparency false

variable {Z E : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℂ E] [BorelSpace E] in
/-- Fatou's lemma gives lower semicontinuity of a nonnegative parameter
integral, including infinite values. -/
theorem lowerSemicontinuousOn_lintegral {f : Z → E → ℝ≥0∞} {U : Set E}
    (σ : Measure Z) (hf : ∀ z, LowerSemicontinuousOn (f z) U)
    (hmeas : Measurable (Function.uncurry f)) :
    LowerSemicontinuousOn (fun c => ∫⁻ z, f z c ∂σ) U := by
  apply lowerSemicontinuousOn_iff_le_liminf.mpr
  intro c hc
  calc
    (∫⁻ z, f z c ∂σ) ≤ ∫⁻ z, liminf (f z) (𝓝[U] c) ∂σ :=
      lintegral_mono fun z => (hf z).le_liminf c hc
    _ ≤ liminf (fun y => ∫⁻ z, f z y ∂σ) (𝓝[U] c) :=
      lintegral_liminf_le (fun y => hmeas.comp (measurable_id.prodMk measurable_const))

/-- A jointly measurable nonnegative family can be integrated while
retaining genuine lower semicontinuity and every complex-line supermean.
The measure may be any s-finite measure, in particular a finite measure. -/
theorem plurisuperharmonic_lintegral {f : Z → E → ℝ≥0∞} {U : Set E}
    (σ : Measure Z) [SFinite σ]
    (hf : ∀ z, PlurisuperharmonicOn (f z) U)
    (hmeas : Measurable (Function.uncurry f)) :
    PlurisuperharmonicOn (fun c => ∫⁻ z, f z c ∂σ) U := by
  refine ⟨lowerSemicontinuousOn_lintegral σ
    (fun z => (hf z).lowerSemicontinuousOn) hmeas, ?_⟩
  intro a b
  have hline : Measurable (fun p : Z × ℂ => f p.1 (a + p.2 • b)) := by
    have ha : Measurable (fun w : ℂ => a + w • b) :=
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
    exact hmeas.comp (measurable_fst.prodMk (ha.comp measurable_snd))
  refine ⟨hline.lintegral_prod_left.aemeasurable, ?_⟩
  intro c r hr hsub
  rw [lintegral_lintegral_swap (f := fun w z => f z (a + w • b))
    (hline.comp measurable_swap).aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun z => ((hf z).onLine a b).supermean c r hr hsub

omit [BorelSpace E] in
/-- Joint measurability of actual logarithmic deficits follows from that
of the actual evaluation map, including the genuine infinite value at zeros. -/
theorem measurable_logDeficit {F : Z → E →L[ℂ] ℂ} (M : ℝ)
    (hF : Measurable (fun p : Z × E => F p.1 p.2)) :
    Measurable (fun p : Z × E => logDeficit (F p.1) M p.2) := by
  unfold logDeficit
  apply Measurable.ite (measurableSet_eq_fun hF measurable_const) measurable_const
  exact ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub hF.norm.log)

/-- Actual linear logarithmic deficits integrated over a parameter measure
are plurisuperharmonic on the given coefficient domain. The only bound is
the actual projection norm bound needed for nonnegative deficits. -/
theorem integrated_logDeficit_plurisuperharmonic
    (σ : Measure Z) [SFinite σ] {F : Z → E →L[ℂ] ℂ} {M : ℝ} {U : Set E}
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hbound : ∀ z c, c ∈ U → ‖F z c‖ ≤ Real.exp M)
    (hF : Measurable (fun p : Z × E => F p.1 p.2)) :
    PlurisuperharmonicOn (fun c => ∫⁻ z, logDeficit (F z) M c ∂σ) U :=
  plurisuperharmonic_lintegral σ
    (fun z => logDeficit_plurisuperharmonic (F z) hU hM (hbound z))
    (measurable_logDeficit M hF)

/-- A continuous family of actual complex-linear projections supplies the
joint measurability input automatically. This covers compact parameter
domains and finite-dimensional coefficient balls with their usual measures. -/
theorem integrated_logDeficit_of_continuous
    [TopologicalSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [SecondCountableTopology E]
    (σ : Measure Z) [SFinite σ] {F : Z → E →L[ℂ] ℂ} {M : ℝ} {U : Set E}
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hbound : ∀ z c, c ∈ U → ‖F z c‖ ≤ Real.exp M)
    (hF : Continuous F) :
    PlurisuperharmonicOn (fun c => ∫⁻ z, logDeficit (F z) M c ∂σ) U := by
  apply integrated_logDeficit_plurisuperharmonic σ hU hM hbound
  exact ((hF.comp continuous_fst).clm_apply continuous_snd).measurable

#print axioms plurisuperharmonic_lintegral
#print axioms integrated_logDeficit_plurisuperharmonic
#print axioms integrated_logDeficit_of_continuous
end V10.PluriPotentialIntegral
