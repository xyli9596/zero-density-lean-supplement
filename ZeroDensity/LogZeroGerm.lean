import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.JensenFormula

/-! Actual scalar logarithms near analytic zeros. These results isolate the
remaining Poincaré–Lelong obligation: the distributional identity for log|z|.
They do not assume that distributional identity or subharmonic compactness. -/
namespace ZeroDensity.LogZeroGerm
open Filter Metric MeromorphicOn InnerProductSpace
open scoped Topology
noncomputable section

/-- Local factorization gives the actual logarithmic singularity and a harmonic
remainder. The multiplicity is the actual analytic zero order. -/
theorem log_norm_local_factorization {v : ℂ → ℂ} {z₀ : ℂ}
    (hv : AnalyticAt ℂ v z₀) (hn : ¬v =ᶠ[𝓝 z₀] 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      HarmonicAt (fun z => Real.log ‖g z‖) z₀ ∧
      ∀ᶠ z in 𝓝 z₀, z ≠ z₀ →
        Real.log ‖v z‖ = (analyticOrderNatAt v z₀ : ℝ) * Real.log ‖z - z₀‖ +
          Real.log ‖g z‖ := by
  have hfinite : analyticOrderAt v z₀ ≠ ⊤ := fun h => hn (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hgn, hfactor⟩ := hv.analyticOrderAt_ne_top.mp hfinite
  refine ⟨g, hg, hgn, hg.harmonicAt_log_norm hgn, ?_⟩
  filter_upwards [hfactor, hg.continuousAt.eventually_ne hgn] with z hf hgz hz
  have hzn : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [hf, norm_smul, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hzn)) (norm_ne_zero_iff.mpr hgz),
    Real.log_pow]

/-- Jensen's exact local bridge from the real logarithm to actual zero
multiplicities. Analyticity is required only near the closed disk. -/
theorem circle_log_minus_center {v : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hv : AnalyticOnNhd ℂ v (closedBall z₀ R)) (hn : v z₀ ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖v z‖) z₀ R - Real.log ‖v z₀‖ =
      ∑ᶠ a, (divisor v (closedBall z₀ R) a : ℝ) * Real.log (R * ‖z₀ - a‖⁻¹) := by
  have ht := AnalyticOnNhd.circleAverage_log_norm (ne_of_gt hR)
    (by simpa [abs_of_pos hR] using hv) hn
  rw [abs_of_pos hR] at ht
  linarith

#print axioms log_norm_local_factorization
#print axioms circle_log_minus_center
end
end ZeroDensity.LogZeroGerm
