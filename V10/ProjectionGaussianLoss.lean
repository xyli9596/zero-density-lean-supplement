import V10.ProjectionGaussian
import Mathlib.Tactic

/-! The actual uniform Gaussian logarithmic integral for every nonzero
complex functional. The extended-valued loss is infinite on its kernel;
the kernel is proved Gaussian-null rather than hidden by `Real.log 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace V10.ProjectionGaussianLoss
open ProjectionGaussian ProjectionGaussianReal
set_option backward.isDefEq.respectTransparency false

def gaussianLogConstant : ℝ :=
  ∫ z : ℂ, |Real.log ‖z‖| ∂complexGaussian ℂ

theorem gaussianLogConstant_nonneg : 0 ≤ gaussianLogConstant :=
  integral_nonneg fun _ => abs_nonneg _

theorem complexGaussian_ae_ne_zero : ∀ᵐ z ∂complexGaussian ℂ, z ≠ 0 := by
  have hrn : ‖Complex.reCLM‖ = 1 := by
    have h := norm_realPart (ContinuousLinearMap.id ℂ ℂ)
    change ‖Complex.reCLM‖ = ‖ContinuousLinearMap.id ℂ ℂ‖ at h
    simpa using h
  have hmap := map_unit_real_complexGaussian Complex.reCLM hrn
  have hr : ∀ᵐ x ∂gaussianReal 0 (1 / 2), x ≠ (0 : ℝ) :=
    (gaussianReal_absolutelyContinuous 0 (v := 1 / 2) (by norm_num)).ae_le (volume.ae_ne 0)
  rw [← hmap] at hr
  have hz := (ae_map_iff Complex.reCLM.measurable.aemeasurable (by measurability)).mp hr
  filter_upwards [hz] with z hz
  exact fun h => hz (by simp [h])

section Functionals
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def normalized (F : E →L[ℂ] ℂ) : E →L[ℂ] ℂ := (‖F‖ : ℂ)⁻¹ • F

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem normalized_norm (F : E →L[ℂ] ℂ) (hF : F ≠ 0) : ‖normalized F‖ = 1 := by
  simp only [normalized, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg F)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hF)

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem normalized_apply_norm (F : E →L[ℂ] ℂ) (x : E) :
    ‖normalized F x‖ = ‖F x‖ / ‖F‖ := by
  simp only [normalized, smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg F), div_eq_mul_inv]
  exact mul_comm _ _

theorem map_normalized_complexGaussian (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    (complexGaussian E).map (normalized F) = complexGaussian ℂ :=
  map_unit_complexGaussian (normalized F) (normalized_norm F hF)

/-- The original functional's kernel is null for the actual Gaussian law. -/
theorem ae_functional_ne_zero (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    ∀ᵐ x ∂complexGaussian E, F x ≠ 0 := by
  have h := complexGaussian_ae_ne_zero
  rw [← map_normalized_complexGaussian F hF] at h
  have hn := (ae_map_iff (normalized F).measurable.aemeasurable (by measurability)).mp h
  filter_upwards [hn] with x hx
  intro he
  apply hx
  simp [normalized, he]

/-- Genuine logarithmic integrability, derived from the projection law. -/
theorem integrable_normalized_log (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    Integrable (fun x => Real.log (‖F x‖ / ‖F‖)) (complexGaussian E) := by
  have h := integrable_log_norm_complexGaussian
  rw [← map_normalized_complexGaussian F hF] at h
  simpa only [Function.comp_def, normalized_apply_norm] using
    h.comp_measurable (normalized F).measurable

/-- The integral equals the same finite one-dimensional complex Gaussian
constant for every nonzero functional, in every finite dimension. -/
theorem integral_abs_normalized_log (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    (∫ x, |Real.log (‖F x‖ / ‖F‖)| ∂complexGaussian E) = gaussianLogConstant := by
  have hm : AEStronglyMeasurable (fun z : ℂ => |Real.log ‖z‖|)
      ((complexGaussian E).map (normalized F)) :=
    measurable_norm.log.abs.aestronglyMeasurable
  have h := integral_map (normalized F).measurable.aemeasurable hm
  rw [map_normalized_complexGaussian F hF] at h
  simpa only [gaussianLogConstant, normalized_apply_norm] using h.symm

/-- The actual absolute logarithmic loss, including infinite values on the
projection kernel as required by the potential-series argument. -/
def loss (F : E →L[ℂ] ℂ) (x : E) : ℝ≥0∞ :=
  if F x = 0 then ∞ else ENNReal.ofReal |Real.log (‖F x‖ / ‖F‖)|

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
theorem measurable_loss (F : E →L[ℂ] ℂ) : Measurable (loss F) := by
  apply Measurable.ite (measurableSet_eq_fun F.measurable measurable_const) measurable_const
  exact (F.measurable.norm.div_const ‖F‖).log.abs.ennreal_ofReal

/-- No uniform integral estimate is a premise: its value and finiteness are
proved for the extended-valued actual logarithmic projection loss. -/
theorem lintegral_loss (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    (∫⁻ x, loss F x ∂complexGaussian E) = ENNReal.ofReal gaussianLogConstant := by
  calc
    (∫⁻ x, loss F x ∂complexGaussian E) =
        ∫⁻ x, ENNReal.ofReal |Real.log (‖F x‖ / ‖F‖)| ∂complexGaussian E := by
      apply lintegral_congr_ae
      filter_upwards [ae_functional_ne_zero F hF] with x hx
      simp only [loss, if_neg hx]
    _ = ENNReal.ofReal (∫ x, |Real.log (‖F x‖ / ‖F‖)| ∂complexGaussian E) :=
      (ofReal_integral_eq_lintegral_ofReal (integrable_normalized_log F hF).abs
        (ae_of_all _ fun _ => abs_nonneg _)).symm
    _ = ENNReal.ofReal gaussianLogConstant := by rw [integral_abs_normalized_log F hF]

theorem lintegral_loss_ne_top (F : E →L[ℂ] ℂ) (hF : F ≠ 0) :
    (∫⁻ x, loss F x ∂complexGaussian E) ≠ ∞ := by
  rw [lintegral_loss F hF]
  exact ENNReal.ofReal_ne_top

end Functionals

#print axioms complexGaussian_ae_ne_zero
#print axioms map_normalized_complexGaussian
#print axioms ae_functional_ne_zero
#print axioms integrable_normalized_log
#print axioms integral_abs_normalized_log
#print axioms lintegral_loss
#print axioms lintegral_loss_ne_top
end V10.ProjectionGaussianLoss
