import V10.ProjectionGaussianSupport
import V10.ProjectionSeries
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! Actual jointly measurable Gaussian projection losses for continuous
families of nonzero complex linear functionals. Tonelli gives the exact
Gaussian integral of the physical-parameter average; the proved bound then
supplies the existing weighted-series theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace V10.ProjectionGaussianFamily
open ProjectionGaussian ProjectionGaussianLoss
set_option backward.isDefEq.respectTransparency false

variable {Z E : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [IsScalarTower ℝ ℂ E] in
/-- Joint measurability is derived from the continuous actual row family. -/
theorem measurable_joint_loss {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) :
    Measurable (fun p : Z × E => loss (F p.1) p.2) := by
  have he : Continuous (fun p : Z × E => F p.1 p.2) :=
    (hF.comp continuous_fst).clm_apply continuous_snd
  apply Measurable.ite (measurableSet_eq_fun he.measurable measurable_const) measurable_const
  exact (he.measurable.norm.div (hF.measurable.comp measurable_fst).norm).log.abs.ennreal_ofReal

def averagedLoss (ν : Measure Z) (F : Z → E →L[ℂ] ℂ) (φ : Z → ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (φ z) * loss (F z) x ∂ν

omit [IsScalarTower ℝ ℂ E] in
theorem measurable_averagedLoss {ν : Measure Z} [SFinite ν]
    {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) {φ : Z → ℝ} (hφ : Measurable φ) :
    Measurable (averagedLoss ν F φ) := by
  apply Measurable.lintegral_prod_left
  exact (hφ.ennreal_ofReal.comp measurable_fst).mul (measurable_joint_loss hF)

/-- Exact Tonelli identity for the actual physical-parameter loss average.
All logarithmic integrals and their common constant are derived upstream. -/
theorem lintegral_averagedLoss {ν : Measure Z} [SFinite ν]
    {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    {φ : Z → ℝ} (hφ : Measurable φ) (hφi : Integrable φ ν) (hφn : ∀ z, 0 ≤ φ z) :
    (∫⁻ x, averagedLoss ν F φ x ∂complexGaussian E) =
      ENNReal.ofReal gaussianLogConstant * ENNReal.ofReal (∫ z, φ z ∂ν) := by
  have hm : Measurable (fun p : Z × E => ENNReal.ofReal (φ p.1) * loss (F p.1) p.2) :=
    (hφ.ennreal_ofReal.comp measurable_fst).mul (measurable_joint_loss hF)
  unfold averagedLoss
  rw [lintegral_lintegral_swap (μ := complexGaussian E) (ν := ν)
    (f := fun x z => ENNReal.ofReal (φ z) * loss (F z) x)
    (hm.comp measurable_swap).aemeasurable]
  simp_rw [lintegral_const_mul'' _ (measurable_loss _).aemeasurable,
    lintegral_loss _ (hFn _)]
  rw [lintegral_mul_const'' _ hφ.ennreal_ofReal.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hφi (ae_of_all _ hφn), mul_comm]

theorem lintegral_averagedLoss_ne_top {ν : Measure Z} [SFinite ν]
    {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    {φ : Z → ℝ} (hφ : Measurable φ) (hφi : Integrable φ ν) (hφn : ∀ z, 0 ≤ φ z) :
    (∫⁻ x, averagedLoss ν F φ x ∂complexGaussian E) ≠ ∞ := by
  rw [lintegral_averagedLoss hF hFn hφ hφi hφn]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The manuscript's reciprocal scales give finite actual loss series
almost everywhere. The uniform logarithmic bound is proved, not assumed. -/
theorem ae_normalized_averagedLoss_summable {ν : Measure Z} [SFinite ν]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0)
    {φ : Z → ℝ} (hφ : Measurable φ) (hφi : Integrable φ ν) (hφn : ∀ z, 0 ≤ φ z)
    (Q : ℕ → ℝ≥0) (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∀ᵐ x ∂complexGaussian E,
      (∀ m, (Q m : ℝ≥0∞)⁻¹ * averagedLoss ν (F m) φ x ≠ ∞) ∧
      Summable (fun m => ((Q m : ℝ≥0∞)⁻¹ * averagedLoss ν (F m) φ x).toNNReal) ∧
      Tendsto (fun m => (Q m : ℝ≥0∞)⁻¹ * averagedLoss ν (F m) φ x) atTop (𝓝 0) := by
  have hw : (∑' m, (Q m : ℝ≥0∞)⁻¹) ≠ ∞ := by
    simp_rw [← ENNReal.coe_inv (ne_of_gt (hQ _))]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hQs
  apply ProjectionSeries.ae_weighted_summable_and_tendsto
    (fun m => averagedLoss ν (F m) φ) (fun m => (Q m : ℝ≥0∞)⁻¹)
    (ENNReal.ofReal gaussianLogConstant * ENNReal.ofReal (∫ z, φ z ∂ν))
    (fun m => (measurable_averagedLoss (hF m) hφ).aemeasurable) _ hw
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  intro m
  exact (lintegral_averagedLoss (hF m) (hFn m) hφ hφi hφn).le

/-- The actual extended sum is finite, before applying `toNNReal`. -/
theorem ae_normalized_averagedLoss_tsum_ne_top {ν : Measure Z} [SFinite ν]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0)
    {φ : Z → ℝ} (hφ : Measurable φ) (hφi : Integrable φ ν) (hφn : ∀ z, 0 ≤ φ z)
    (Q : ℕ → ℝ≥0) (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∀ᵐ x ∂complexGaussian E,
      (∑' m, (Q m : ℝ≥0∞)⁻¹ * averagedLoss ν (F m) φ x) ≠ ∞ := by
  have hw : (∑' m, (Q m : ℝ≥0∞)⁻¹) ≠ ∞ := by
    simp_rw [← ENNReal.coe_inv (ne_of_gt (hQ _))]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hQs
  exact ProjectionSeries.ae_weighted_tsum_ne_top
    (fun m => averagedLoss ν (F m) φ) (fun m => (Q m : ℝ≥0∞)⁻¹)
    (ENNReal.ofReal gaussianLogConstant * ENNReal.ofReal (∫ z, φ z ∂ν))
    (fun m => (measurable_averagedLoss (hF m) hφ).aemeasurable)
    (fun m => (lintegral_averagedLoss (hF m) (hFn m) hφ hφi hφn).le) hw
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Every ball contains an initial vector for which the actual reciprocal-
normalized loss series is summable. -/
theorem exists_summable_in_ball {ν : Measure Z} [SFinite ν]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0)
    {φ : Z → ℝ} (hφ : Measurable φ) (hφi : Integrable φ ν) (hφn : ∀ z, 0 ≤ φ z)
    (Q : ℕ → ℝ≥0) (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹))
    (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Metric.ball c r,
      (∑' m, (Q m : ℝ≥0∞)⁻¹ * averagedLoss ν (F m) φ x) ≠ ∞ := by
  apply ProjectionGaussianSupport.exists_good_in_ball _ c hr
  exact ae_normalized_averagedLoss_tsum_ne_top hF hFn hφ hφi hφn Q hQ hQs

#print axioms measurable_joint_loss
#print axioms lintegral_averagedLoss
#print axioms ae_normalized_averagedLoss_summable
#print axioms exists_summable_in_ball
end V10.ProjectionGaussianFamily
