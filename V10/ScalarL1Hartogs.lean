import V10.ScalarLogSubmean
import V10.ScalarAnalytic
import Ray.Hartogs.FubiniBall
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!+# Quantitative local upper bounds from scalar L¹ convergence

The error is controlled by the actual L¹ integral on a larger set. The disk
submean input will be supplied by the analytic-log theorem, which treats zeros
by continuous truncations. These results do not assume pointwise convergence.
-/

noncomputable section
open Filter MeasureTheory Metric Set
open scoped Topology
namespace V10.ScalarL1Hartogs
set_option backward.isDefEq.respectTransparency false

theorem average_le_const_add_L1 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u H : α → ℝ} {B : ℝ}
    (hm : 0 < μ.real univ) (hu : Integrable u μ) (hH : Integrable H μ)
    (hb : ∀ᵐ z ∂μ, H z ≤ B) :
    (⨍ z, u z ∂μ) ≤ B + (μ.real univ)⁻¹ * ∫ z, ‖u z - H z‖ ∂μ := by
  have hi := integral_mono_ae hu (((hu.sub hH).norm).add (integrable_const B))
    (hb.mono fun z hz => by
      change u z ≤ ‖u z - H z‖ + B
      have h := le_abs_self (u z - H z)
      simp only [Real.norm_eq_abs]
      linarith)
  change (∫ z, u z ∂μ) ≤ ∫ z, ‖u z - H z‖ + B ∂μ at hi
  have hdiff : Integrable (fun z => ‖u z - H z‖) μ := (hu.sub hH).norm
  rw [integral_add hdiff (integrable_const B), integral_const] at hi
  simp only [smul_eq_mul] at hi
  rw [average_eq, smul_eq_mul]
  calc
    _ ≤ (μ.real univ)⁻¹ * ((∫ z, ‖u z - H z‖ ∂μ) + μ.real univ * B) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hm.le)
    _ = B + (μ.real univ)⁻¹ * ∫ z, ‖u z - H z‖ ∂μ := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul, add_comm]

/-- A uniform-radius disk estimate, with error measured on the larger set D. -/
theorem disk_upper_bound {u H : ℂ → ℝ} {D : Set ℂ} {x : ℂ} {r B : ℝ}
    (hr : 0 < r) (hD : closedBall x r ⊆ D)
    (hu : IntegrableOn u D) (hH : IntegrableOn H D)
    (hb : ∀ᵐ z ∂volume.restrict D, H z ≤ B)
    (hsub : u x ≤ ⨍ z in closedBall x r, u z) :
    u x ≤ B + (Real.pi * r ^ 2)⁻¹ * ∫ z in D, ‖u z - H z‖ := by
  let : IsFiniteMeasure (volume.restrict (closedBall x r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x r).measure_ne_top
  have hm : 0 < (volume.restrict (closedBall x r)).real univ := by
    rw [measureReal_restrict_apply_univ, Complex.volume_closedBall' hr.le]
    positivity
  have hbb : ∀ᵐ z ∂volume.restrict (closedBall x r), H z ≤ B :=
    hb.filter_mono (ae_mono (Measure.restrict_mono hD le_rfl))
  have hav := average_le_const_add_L1 hm (hu.mono_set hD) (hH.mono_set hD) hbb
  rw [measureReal_restrict_apply_univ, Complex.volume_closedBall' hr.le] at hav
  have hi : (∫ z in closedBall x r, ‖u z - H z‖) ≤ ∫ z in D, ‖u z - H z‖ := by
    exact setIntegral_mono_set (hu.sub hH).norm (ae_of_all _ fun _ => norm_nonneg _)
      (ae_of_all _ fun _ hz => hD hz)
  exact hsub.trans (hav.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (Real.pi * r ^ 2)⁻¹)) B))

/-- Genuine L¹ convergence supplies eventual uniform upper bounds wherever
fixed-radius disks fit in D and disk submean inequalities hold. -/
theorem eventually_uniform_upper_of_L1 {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → ℝ} {H : ℂ → ℝ} {D K : Set ℂ} {r B : ℝ}
    (hr : 0 < r) (hD : ∀ x ∈ K, closedBall x r ⊆ D)
    (hu : ∀ i, IntegrableOn (u i) D) (hH : IntegrableOn H D)
    (hb : ∀ᵐ z ∂volume.restrict D, H z ≤ B)
    (hsub : ∀ i x, x ∈ K → u i x ≤ ⨍ z in closedBall x r, u i z)
    (hL1 : Tendsto (fun i => ∫ z in D, ‖u i z - H z‖) l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ K, u i x ≤ B + ε := by
  intro ε hε
  have ht : Tendsto (fun i => (Real.pi * r ^ 2)⁻¹ * ∫ z in D, ‖u i z - H z‖)
      l (𝓝 0) := by simpa only [mul_zero] using hL1.const_mul (Real.pi * r ^ 2)⁻¹
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with i hi x hx
  exact (disk_upper_bound hr (hD x hx) (hu i) hH hb (hsub i x hx)).trans
    (add_le_add_right hi.le B)

/-- Quantitative upper bound for an actual analytic scalar function. It is
valid even at scalar zeros, because the conclusion is expressed on the norm. -/
theorem analytic_norm_upper_bound {f : ℂ → ℂ} {H : ℂ → ℝ}
    {D : Set ℂ} {x : ℂ} {r q B : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hD : closedBall x r ⊆ D)
    (hf : AnalyticOnNhd ℂ f D)
    (hz : ∀ᵐ z ∂volume.restrict D, f z ≠ 0)
    (hi : IntegrableOn (fun z => Real.log ‖f z‖) D)
    (hH : IntegrableOn H D) (hb : ∀ᵐ z ∂volume.restrict D, H z ≤ B) :
    ‖f x‖ ≤ Real.exp ((B + (Real.pi * r ^ 2)⁻¹ *
      ∫ z in D, ‖Real.log ‖f z‖ / q - H z‖) * q) := by
  by_cases hx : f x = 0
  · rw [hx, norm_zero]
    exact (Real.exp_pos _).le
  have hs := ScalarLogSubmean.normalized_log_norm_le_disk_average hr hq (hf.mono hD) hx
    (hz.filter_mono (ae_mono (Measure.restrict_mono hD le_rfl))) (hi.mono_set hD)
  have hb' := disk_upper_bound hr hD (hi.div_const q) hH hb hs
  exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hx)).mp ((div_le_iff₀ hq).mp hb')

/-- The L¹ version of a local Hartogs upper bound for normalized analytic logs.
No pointwise bound or pointwise convergence hypothesis is required. -/
theorem analytic_norm_eventually_uniform_upper_of_L1 {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {q : ι → ℝ} {H : ℂ → ℝ} {D K : Set ℂ} {r B : ℝ}
    (hr : 0 < r) (hD : ∀ x ∈ K, closedBall x r ⊆ D)
    (hq : ∀ i, 0 < q i) (hA : ∀ i, AnalyticOnNhd ℂ (F i) D)
    (hz : ∀ i, ∀ᵐ z ∂volume.restrict D, F i z ≠ 0)
    (hi : ∀ i, IntegrableOn (fun z => Real.log ‖F i z‖) D)
    (hH : IntegrableOn H D) (hb : ∀ᵐ z ∂volume.restrict D, H z ≤ B)
    (hL1 : Tendsto (fun i => ∫ z in D, ‖Real.log ‖F i z‖ / q i - H z‖) l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ K, ‖F i x‖ ≤ Real.exp ((B + ε) * q i) := by
  intro ε hε
  have ht : Tendsto (fun i => (Real.pi * r ^ 2)⁻¹ *
      ∫ z in D, ‖Real.log ‖F i z‖ / q i - H z‖) l (𝓝 0) := by
    simpa only [mul_zero] using hL1.const_mul (Real.pi * r ^ 2)⁻¹
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with i hi' x hx
  apply (analytic_norm_upper_bound hr (hq i) (hD x hx) (hA i) (hz i) (hi i) hH hb).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by linarith) (hq i).le

/-- Specialization to the actual scaled solution: analytic nonzero germs,
null zero sets and log integrability are derived from one nonzero jet. -/
theorem scaled_solution_norm_upper_bound {n : ℕ} {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    {R r B : ℝ} {x : ℂ} {H : ℂ → ℝ}
    (hR : 0 < R) (hr : 0 < r) (hD : IsCompact D)
    (hDS : ∀ z ∈ D, (R : ℂ) * z ∈ S) (hball : closedBall x r ⊆ D)
    (hH : IntegrableOn H D) (hb : ∀ᵐ z ∂volume.restrict D, H z ≤ B) :
    ‖v ((R : ℂ) * x)‖ ≤ Real.exp ((B + (Real.pi * r ^ 2)⁻¹ *
      ∫ z in D, ‖ScalarAnalytic.potential v R z - H z‖) * R) := by
  have hA := ScalarAnalytic.dilated_analyticOnNhd hv hDS
  have hg := ScalarAnalytic.germs_ne_zero_of_jet hS hconn hv hz₀ hn
  have hgn : ∀ z ∈ D, ¬(fun w => v ((R : ℂ) * w)) =ᶠ[𝓝 z] 0 :=
    fun z hz => ScalarAnalytic.dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')
      (hg _ (hDS z hz))
  exact analytic_norm_upper_bound hr hR hball hA
    (ScalarAnalytic.ae_ne_zero_of_germs hD.measurableSet hA hgn)
    ((ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm hA hgn).integrableOn_isCompact hD)
    hH hb

#print axioms average_le_const_add_L1
#print axioms disk_upper_bound
#print axioms eventually_uniform_upper_of_L1
#print axioms analytic_norm_upper_bound
#print axioms analytic_norm_eventually_uniform_upper_of_L1
#print axioms scaled_solution_norm_upper_bound
end V10.ScalarL1Hartogs
