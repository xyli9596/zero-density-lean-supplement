import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Genuine local Lebesgue integrability of the planar logarithmic kernel.
At the single singular point we use mathlib's real representative log 0 = 0;
changing that value does not affect the local integral or distributions. -/
namespace ZeroDensity.PlanarLogIntegrability
open MeasureTheory Set Metric
open scoped Topology
noncomputable section

lemma abs_log_bound_on_ball {R : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ‖Real.log ‖z‖‖ ≤ max 1 (R ^ 2) * ‖z‖ ^ (- (1 : ℝ)) := by
  have hn : ‖z‖ < R := mem_ball_zero_iff.mp hz
  by_cases hzero : ‖z‖ = 0
  · simp [hzero]
  have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  rw [Real.rpow_neg_one]
  by_cases hsmall : ‖z‖ ≤ 1
  · have hl : 0 ≤ -Real.log ‖z‖ := neg_nonneg.mpr (Real.log_nonpos hp.le hsmall)
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at hi
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hp.le hsmall)]
    have hc : 1 ≤ max 1 (R ^ 2) := le_max_left _ _
    nlinarith [inv_pos.mpr hp]
  · have hlarge : 1 ≤ ‖z‖ := le_of_not_ge hsmall
    have hl := Real.log_le_sub_one_of_pos hp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hlarge)]
    have hr : 0 < R := hp.trans hn
    have hs : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith
    have hc : R ^ 2 ≤ max 1 (R ^ 2) := le_max_right _ _
    apply (le_div_iff₀ hp).mpr
    nlinarith

/-- The actual planar scalar logarithmic kernel is integrable on every bounded
ball. The domination exponent is one, strictly smaller than real dimension two. -/
theorem integrableOn_log_norm_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by norm_num [Complex.finrank_real_complex] : 1 ≤ Module.finrank ℝ ℂ)
    (C := max 1 (R ^ 2)) (α := (1 : ℝ))
    (by norm_num [Complex.finrank_real_complex])
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact abs_log_bound_on_ball hz
  · exact measurable_norm.log.aestronglyMeasurable

/-- Actual local integrability on the complex plane, including the origin. -/
theorem locallyIntegrable_log_norm :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_log_norm_ball R).mono_set fun z hz => mem_ball_zero_iff.mpr (hbound z hz)

/-- Translation preserves local integrability of the actual logarithmic
singularity at any prescribed complex point. -/
theorem locallyIntegrable_log_norm_sub (a : ℂ) :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z - a‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hi := locallyIntegrable_log_norm.integrableOn_isCompact
    (hK.image (continuous_id.add (continuous_const (y := -a))))
  have ht := (measurePreserving_add_right volume (-a)).integrableOn_image
    (Homeomorph.addRight (-a)).measurableEmbedding (f := fun z => Real.log ‖z‖) (s := K)
  simpa only [Function.comp_def, sub_eq_add_neg] using ht.mp hi

/-- The Cauchy kernel is locally integrable in real dimension two. This
provides the integrable first-derivative kernel needed by integration by parts. -/
theorem integrableOn_inverse_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => z⁻¹) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by norm_num [Complex.finrank_real_complex] : 1 ≤ Module.finrank ℝ ℂ)
    (C := (1 : ℝ)) (α := (1 : ℝ))
    (by norm_num [Complex.finrank_real_complex])
  · exact Filter.Eventually.of_forall fun z => by simp [Real.rpow_neg_one]
  · exact measurable_inv.aestronglyMeasurable

theorem locallyIntegrable_inverse : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_inverse_ball R).mono_set fun z hz => mem_ball_zero_iff.mpr (hbound z hz)

#print axioms abs_log_bound_on_ball
#print axioms integrableOn_log_norm_ball
#print axioms locallyIntegrable_log_norm
#print axioms locallyIntegrable_log_norm_sub
#print axioms locallyIntegrable_inverse
end
end ZeroDensity.PlanarLogIntegrability
