import V10.ScalarCauchyNoncollapse
import Mathlib.Tactic

/-!+# Actual scalar inputs to local logarithmic compactness

The local upper bound and the moving nonzero sample are derived from the
already proved vector-potential convergence and the actual Cauchy estimates.
They are not additional asymptotic assumptions on the scalar logarithm.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.ScalarCompactnessInputs
set_option backward.isDefEq.respectTransparency false

theorem eventually_uniform_scalar_bound {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {K : Set ℂ} {H : ℂ → ℝ}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hlim : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop K)
    (hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ K, ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ R : ℝ in atTop, ∀ z ∈ K,
      ‖v ((R : ℂ) * z)‖ ≤ Real.exp (R * B) := by
  obtain ⟨b, hb⟩ := hK.bddAbove_image hH
  refine ⟨max 0 (b + 1), le_max_left _ _, ?_⟩
  have hu := (Metric.tendstoUniformlyOn_iff.mp hlim) 1 zero_lt_one
  filter_upwards [hu, hjet, eventually_gt_atTop (0 : ℝ)] with R hU hJ hR z hz
  have hdist := hU z hz
  have hzbound : H z ≤ b := hb (mem_image_of_mem H hz)
  have hp : PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v) R z ≤ max 0 (b + 1) := by
    have hd : |H z - PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v) R z| < 1 :=
      by simpa only [Real.dist_eq] using hdist
    have := neg_le_abs (H z - PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v) R z)
    linarith [le_max_right 0 (b + 1)]
  have hlog : Real.log ‖ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z)‖ ≤ R * max 0 (b + 1) := by
    have h := (div_le_iff₀ hR).mp hp
    simpa only [mul_comm] using h
  have hnrm := (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hJ z hz))).mp hlog
  exact (ZeroDensity.ScalarLimit.norm_scalar_le_jet hn v _).trans hnrm

/-- The hypotheses of moving-center analytic compactness follow from actual
jet compact convergence on a slightly larger scaled disk. -/
theorem eventual_local_analytic_bounds {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {S : Set ℂ} {H : ℂ → ℝ} {x : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hv : AnalyticOnNhd ℂ v S)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (5 * δ), (R : ℂ) * z ∈ S)
    (hH : ContinuousOn H (closedBall x (5 * δ)))
    (hlim : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop (closedBall x (5 * δ)))
    (hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (5 * δ),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ᶠ R : ℝ in atTop, 1 ≤ R ∧
      AnalyticOnNhd ℂ (fun z => v ((R : ℂ) * z)) (closedBall x (5 * δ)) ∧
      (∀ z ∈ closedBall x (5 * δ), ‖v ((R : ℂ) * z)‖ ≤ Real.exp (R * B)) ∧
      ∃ a ∈ closedBall x δ, Real.exp (-R * C) ≤ ‖v ((R : ℂ) * a)‖ := by
  have hxx : x ∈ closedBall x (5 * δ) := mem_closedBall_self (by positivity)
  obtain ⟨B, hB, hu⟩ := eventually_uniform_scalar_bound hn (isCompact_closedBall x (5 * δ)) hH hlim hjet
  have hphys : ∀ᶠ R : ℝ in atTop,
      AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ)) := by
    filter_upwards [hDS, eventually_gt_atTop (0 : ℝ)] with R hD hR
    apply hv.mono
    intro w hw
    have hz := ScalarCauchyNoncollapse.rescaled_mem_closedBall hR hw
    have hz' : (R : ℂ)⁻¹ * w ∈ closedBall x (5 * δ) :=
      closedBall_subset_closedBall (by linarith) hz
    have hc := hD _ hz'
    simpa only [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_mul] using hc
  have hpoint := hlim.tendsto_at hxx
  have hj : ∀ᶠ R : ℝ in atTop, ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x) ≠ 0 :=
    hjet.mono fun _ h => h x hxx
  have hl := ScalarCauchyNoncollapse.eventually_exists_scalar_lower_sample hδ hphys hj hpoint
    (H x - 1) (by linarith)
  let C : ℝ := max 1 (1 - H x)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [hDS, hu, hl, eventually_ge_atTop (1 : ℝ)] with R hD hup hlo hR
  obtain ⟨a, ha, _, hlow⟩ := hlo
  refine ⟨hR, ScalarAnalytic.dilated_analyticOnNhd hv hD, hup, a, ha, ?_⟩
  apply le_trans _ hlow
  apply Real.exp_le_exp.mpr
  have hC' : 1 - H x ≤ C := le_max_right _ _
  nlinarith

#print axioms eventually_uniform_scalar_bound
#print axioms eventual_local_analytic_bounds
end V10.ScalarCompactnessInputs
