import V10.ScalarAnalytic
import V10.PerronVectorLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!+# Cauchy comparison and noncollapse of the actual scalar potentials

A maximum on a fixed scaled disk supplies an actual nonzero scalar sample
whose logarithmic rate is bounded below by the jet rate, up to `(log C)/R`.
The sample point may vary with R; no pointwise scalar convergence is assumed.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.ScalarCauchyNoncollapse
set_option backward.isDefEq.respectTransparency false

lemma rescaled_mem_closedBall {R δ : ℝ} {x w : ℂ} (hR : 0 < R)
    (hw : w ∈ closedBall ((R : ℂ) * x) (R * δ)) :
    (R : ℂ)⁻¹ * w ∈ closedBall x δ := by
  have hn : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have he : (R : ℂ)⁻¹ * w - x = (R : ℂ)⁻¹ * (w - (R : ℂ) * x) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [mem_closedBall, dist_eq_norm, he, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  have hw' : ‖w - (R : ℂ) * x‖ ≤ R * δ := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hw
  calc
    R⁻¹ * ‖w - (R : ℂ) * x‖ ≤ R⁻¹ * (R * δ) :=
      mul_le_mul_of_nonneg_left hw' (inv_nonneg.mpr hR.le)
    _ = δ := by field_simp

/-- A bound on the scaled disk gives a bound on the original physical jet. -/
theorem jet_bound_of_scaled_disk {n : ℕ} {v : ℂ → ℂ} {R δ M : ℝ} {x : ℂ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hv : AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ)))
    (hb : ∀ z ∈ closedBall x δ, ‖v ((R : ℂ) * z)‖ ≤ M) :
    ‖ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x)‖ ≤
      ZeroDensity.ScalarLimit.cauchyConstant n δ * M := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply ZeroDensity.ScalarLimit.jet_bound_scaled_disk hR hδ hM
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (mul_pos hRp hδ).ne']
    exact hv.differentiableOn
  · intro w hw
    have hz := rescaled_mem_closedBall hRp (sphere_subset_closedBall hw)
    have hn : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRp.ne'
    simpa only [← mul_assoc, mul_inv_cancel₀ hn, one_mul] using hb _ hz

/-- An actual scalar sample in the scaled disk controls the whole original
jet. Compactness is used only for the finite-dimensional scalar maximum here. -/
theorem exists_scalar_sample {n : ℕ} {v : ℂ → ℂ} {R δ : ℝ} {x : ℂ}
    (hR : 1 ≤ R) (hδ : 0 < δ)
    (hv : AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ))) :
    ∃ z ∈ closedBall x δ,
      ‖ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x)‖ ≤
        ZeroDensity.ScalarLimit.cauchyConstant n δ * ‖v ((R : ℂ) * z)‖ := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmaps : ∀ z ∈ closedBall x δ,
      (R : ℂ) * z ∈ closedBall ((R : ℂ) * x) (R * δ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hRp]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hz) hRp.le
  have hc : ContinuousOn (fun z => ‖v ((R : ℂ) * z)‖) (closedBall x δ) :=
    (ScalarAnalytic.dilated_analyticOnNhd hv hmaps).continuousOn.norm
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall x δ).exists_isMaxOn
    (nonempty_closedBall.mpr hδ.le) hc
  exact ⟨z, hz, jet_bound_of_scaled_disk hR hδ (norm_nonneg _) hv hmax⟩

/-- The Cauchy sample is nonzero when the actual derivative jet is nonzero. -/
theorem exists_scalar_log_sample {n : ℕ} {v : ℂ → ℂ} {R δ : ℝ} {x : ℂ}
    (hR : 1 ≤ R) (hδ : 0 < δ)
    (hv : AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ)))
    (hn : ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x) ≠ 0) :
    ∃ z ∈ closedBall x δ, v ((R : ℂ) * z) ≠ 0 ∧
      PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v) R x -
        Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R ≤
        ScalarAnalytic.potential v R z := by
  obtain ⟨z, hz, hb⟩ := exists_scalar_sample (n := n) hR hδ hv
  have hnp := norm_pos_iff.mpr hn
  have hzn : v ((R : ℂ) * z) ≠ 0 := by
    intro he
    rw [he, norm_zero, mul_zero] at hb
    exact (not_le_of_gt hnp) hb
  have hCp := ZeroDensity.ScalarLimit.cauchyConstant_pos (n := n) hδ
  have hh := Real.log_le_log hnp hb
  rw [Real.log_mul hCp.ne' (norm_pos_iff.mpr hzn).ne'] at hh
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hd := div_le_div_of_nonneg_right hh hRp.le
  refine ⟨z, hz, hzn, ?_⟩
  dsimp [PerronVectorLimit.potential, ScalarAnalytic.potential]
  rw [add_div] at hd
  linarith

/-- A finite actual jet rate prevents collapse of scalar logarithms on a
scaled disk. The scalar point is chosen from the function, not postulated. -/
theorem eventually_exists_scalar_lower_sample {n : ℕ} {v : ℂ → ℂ}
    {δ L : ℝ} {x : ℂ} (hδ : 0 < δ)
    (hv : ∀ᶠ R : ℝ in atTop,
      AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ)))
    (hn : ∀ᶠ R : ℝ in atTop, ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x) ≠ 0)
    (hlim : Tendsto (fun R => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) R x) atTop (𝓝 L)) :
    ∀ B < L, ∀ᶠ R : ℝ in atTop, ∃ z ∈ closedBall x δ,
      v ((R : ℂ) * z) ≠ 0 ∧ Real.exp (B * R) ≤ ‖v ((R : ℂ) * z)‖ := by
  intro B hB
  have he : Tendsto (fun R : ℝ =>
      Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun R => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) R x -
      Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R) atTop (𝓝 L) := by
    simpa only [sub_zero] using hlim.sub he
  filter_upwards [hv, hn, eventually_ge_atTop (1 : ℝ), hl.eventually (lt_mem_nhds hB)]
    with R hA hnonzero hR hrate
  obtain ⟨z, hz, hzn, hlog⟩ := exists_scalar_log_sample hR hδ hA hnonzero
  refine ⟨z, hz, hzn, ?_⟩
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb : B ≤ Real.log ‖v ((R : ℂ) * z)‖ / R := hrate.le.trans hlog
  exact (Real.le_log_iff_exp_le (norm_pos_iff.mpr hzn)).mp ((le_div_iff₀ hRp).mp hb)

/-- Excludes the locally uniform minus-infinity alternative in the norm
formulation, which remains meaningful at scalar zeros. -/
theorem not_uniform_scalar_collapse {n : ℕ} {v : ℂ → ℂ}
    {δ L : ℝ} {x : ℂ} (hδ : 0 < δ)
    (hv : ∀ᶠ R : ℝ in atTop,
      AnalyticOnNhd ℂ v (closedBall ((R : ℂ) * x) (R * δ)))
    (hn : ∀ᶠ R : ℝ in atTop, ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * x) ≠ 0)
    (hlim : Tendsto (fun R => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) R x) atTop (𝓝 L)) :
    ¬∀ B : ℝ, ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x δ,
      ‖v ((R : ℂ) * z)‖ ≤ Real.exp (B * R) := by
  intro hcollapse
  have hlo := eventually_exists_scalar_lower_sample hδ hv hn hlim (L - 1) (by linarith)
  have hup := hcollapse (L - 2)
  obtain ⟨R, hR, ⟨z, hz, _, hlow⟩, hupp⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hlo.and hup)).exists
  have he := hlow.trans (hupp z hz)
  have he' := Real.exp_le_exp.mp he
  nlinarith

#print axioms jet_bound_of_scaled_disk
#print axioms exists_scalar_sample
#print axioms exists_scalar_log_sample
#print axioms eventually_exists_scalar_lower_sample
#print axioms not_uniform_scalar_collapse
end V10.ScalarCauchyNoncollapse
