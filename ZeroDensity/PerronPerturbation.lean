import ZeroDensity.PerronEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Vanishing unit-window perturbation bounds required by the classical
Perron theorem. The spectral classification itself is not supplied here. -/
noncomputable section
namespace ZeroDensity.PerronPerturbation
open Filter Set
open scoped Topology Interval

/-- Pointwise vanishing implies vanishing averages on every fixed unit window.
The estimate also holds for totalized integrals; continuous ODE perturbations
in the intended application are genuinely interval-integrable. -/
theorem unit_window_integral_tendsto_zero {γ : ℝ → ℝ}
    (hγ : Tendsto γ atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => ∫ s in r..r+1, γ s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : 0 < ε/2 := half_pos hε
  have hsmall : ∀ᶠ s in atTop, ‖γ s‖ < ε/2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hγ.eventually (Metric.ball_mem_nhds 0 he)
  obtain ⟨R,hR⟩ := eventually_atTop.mp hsmall
  refine ⟨R,?_⟩
  intro r hr
  have hb : ‖∫ s in r..r+1, γ s‖ ≤ ε/2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := r) (b := r+1) (C := ε/2) (f := γ) (fun s hs => ?_)
    · simpa using hh
    · have hle : r ≤ r+1 := by linarith
      rw [uIoc_of_le hle] at hs
      exact (hR s (hr.trans hs.1.le)).le
  simpa only [dist_zero_right] using hb.trans_lt (by linarith : ε/2 < ε)

/-- The actual operator perturbation norm tends to zero. -/
theorem perturbation_norm_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℝ → E →L[ℝ] E} {B₀ : E →L[ℝ] E}
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun r => ‖B r-B₀‖) atTop (𝓝 0) := by
  simpa only [sub_self,norm_zero] using (hB.sub_const B₀).norm

/-- The norm of the genuine asymptotically constant coefficient error satisfies
Perron's unit-window smallness condition. No L1 assumption is introduced. -/
theorem perturbation_unit_window_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℝ → E →L[ℝ] E} {B₀ : E →L[ℝ] E}
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun r : ℝ => ∫ s in r..r+1, ‖B s-B₀‖) atTop (𝓝 0) :=
  unit_window_integral_tendsto_zero (perturbation_norm_tendsto_zero hB)

#print axioms unit_window_integral_tendsto_zero
#print axioms perturbation_norm_tendsto_zero
#print axioms perturbation_unit_window_tendsto_zero
end ZeroDensity.PerronPerturbation
