import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Tactic

/-! Actual Gaussian logarithmic integrability. The logarithmic singularity
is controlled by local Lebesgue integrability and the bounded Gaussian
density; the tail is controlled by the genuine Gaussian first moment.
No logarithmic integrability or uniform integral bound is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace V10.ProjectionGaussianReal

/-- The absolute logarithm is integrable for every nondegenerate real
Gaussian law, including its genuine logarithmic singularity at zero. -/
theorem integrable_log_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable Real.log (gaussianReal m v) := by
  have hlocal : IntegrableOn Real.log (Icc (-1 : ℝ) 1) (gaussianReal m v) := by
    have hl : IntegrableOn Real.log (Icc (-1 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
        intervalIntegral.intervalIntegrable_log'
    have hp : Continuous (gaussianPDFReal m v) := by
      unfold gaussianPDFReal
      fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hp.norm.continuousOn
    rw [IntegrableOn, gaussianReal_of_var_ne_zero m hv, restrict_withDensity measurableSet_Icc,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF m v)
        (ae_of_all _ fun x => by simp [gaussianPDF])]
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
    apply hl.bdd_mul hp.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC ⟨x, hx, rfl⟩
  have htail : IntegrableOn Real.log (Icc (-1 : ℝ) 1)ᶜ (gaussianReal m v) := by
    have hid : Integrable (fun x : ℝ => ‖x‖) (gaussianReal m v) :=
      IsGaussian.integrable_id.norm
    apply hid.integrableOn.mono' Real.measurable_log.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    have hx' : 1 ≤ |x| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]
        linarith
      · exact le_trans (by linarith) (le_abs_self x)
    rw [Real.norm_eq_abs, ← Real.log_abs, abs_of_nonneg (Real.log_nonneg hx'),
      Real.norm_eq_abs]
    exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx')).trans (by linarith)
  simpa only [union_compl_self, integrableOn_univ] using hlocal.union htail

theorem integrable_abs_log_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => |Real.log (|x|)|) (gaussianReal m v) := by
  simpa only [Real.log_abs] using (integrable_log_gaussianReal m hv).abs

/-- The real part of a complex functional has exactly the same operator
norm. This supplies a nondegenerate one-dimensional Gaussian projection. -/
theorem norm_realPart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (F : E →L[ℂ] ℂ) :
    ‖Complex.reCLM.comp (F.restrictScalars ℝ)‖ = ‖F‖ := by
  exact (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm.norm_map F

/-- An actual normalized real linear projection of standard Gaussian
measure has the standard one-dimensional Gaussian law. -/
theorem map_unit_real_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ = 1) :
    (stdGaussian E).map L = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hL]
  norm_num

#print axioms integrable_log_gaussianReal
#print axioms integrable_abs_log_gaussianReal
#print axioms norm_realPart
#print axioms map_unit_real_stdGaussian
end V10.ProjectionGaussianReal
