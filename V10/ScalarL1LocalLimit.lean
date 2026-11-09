import V10.ScalarCompactnessActual
import V10.ScalarL1Identification
import V10.ScalarL1Convergence
import Mathlib.Tactic

/-!
# Full-parameter scalar L¹ convergence on an interior disk

Actual analytic-log compactness supplies a subsequence on a larger disk.
The actual jet limit identifies its L¹ limit on the disk interior: the
upper bound follows from scalar ≤ jet almost everywhere, and the lower
bound from Cauchy samples and Lebesgue differentiation. Restriction to a
strictly smaller disk avoids imposing values on null circle boundaries.
The subsequence criterion then gives convergence for every real R → ∞.
-/

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology
namespace V10.ScalarL1LocalLimit
set_option backward.isDefEq.respectTransparency false

/-- The scalar L¹ conclusion on a fixed local disk, from the actual analytic
solution and the already established locally uniform actual jet limit.
Neither scalar compactness nor identification is an input. -/
theorem actual_scalar_L1_tendsto_on_closedBall {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {S : Set ℂ} {H : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hv : AnalyticOnNhd ℂ v S)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (10 * r), (R : ℂ) * z ∈ S)
    (hH : ContinuousOn H (closedBall c (10 * r)))
    (hlim : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop (closedBall c (10 * r)))
    (hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (10 * r),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0) :
    Tendsto (fun R : ℝ => ∫ z in closedBall c r,
      ‖ScalarAnalytic.potential v R z - H z‖) atTop (𝓝 0) := by
  let D := closedBall c (2 * r)
  let K := closedBall c r
  have hDbig : D ⊆ closedBall c (10 * r) := closedBall_subset_closedBall (by linarith)
  have hKD : K ⊆ D := closedBall_subset_closedBall (by linarith)
  have hKint : K ⊆ interior D :=
    (closedBall_subset_ball (by linarith : r < 2 * r)).trans ball_subset_interior_closedBall
  have hDc : IsCompact D := isCompact_closedBall c (2 * r)
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDc.measure_ne_top
  obtain ⟨T₀, hT₀S, hT₀jet⟩ := (hDS.and hjet).exists
  have hc : c ∈ closedBall c (10 * r) := mem_closedBall_self (by positivity)
  have hz₀ := hT₀S c hc
  have hn₀ := hT₀jet c hc
  apply ScalarL1Convergence.L1_tendsto_of_subsequence_limits_ae
  intro R hRt
  have hrad : 5 * (2 * r) = 10 * r := by ring
  have hDS' : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (5 * (2 * r)), (R : ℂ) * z ∈ S := by
    simpa only [hrad] using hDS
  have hH' : ContinuousOn H (closedBall c (5 * (2 * r))) := by
    simpa only [hrad] using hH
  have hlim' : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop (closedBall c (5 * (2 * r))) := by
    simpa only [hrad] using hlim
  have hjet' : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (5 * (2 * r)),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0 := by
    simpa only [hrad] using hjet
  obtain ⟨σ, hσ, U, hUi, hUlim⟩ :=
    ScalarCompactnessActual.actual_scalar_local_L1_subsequence hn (by linarith : 0 < 2 * r)
      hv hDS' hH' hlim' hjet' hRt
  have hRσ : Tendsto (fun k => R (σ k)) atTop atTop := hRt.comp hσ.tendsto_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hRσ.eventually ((eventually_ge_atTop (1 : ℝ)).and (hDS.and hjet)))
  let τ : ℕ → ℕ := fun k => σ (k + N)
  have hτ : StrictMono τ := fun i j hij => hσ (Nat.add_lt_add_right hij N)
  let T : ℕ → ℝ := fun k => R (τ k)
  have hTt : Tendsto T atTop atTop := hRt.comp hτ.tendsto_atTop
  have htail (k : ℕ) : 1 ≤ T k ∧
      (∀ z ∈ closedBall c (10 * r), (T k : ℂ) * z ∈ S) ∧
      ∀ z ∈ closedBall c (10 * r), ZeroDensity.ScalarLimit.jet n v ((T k : ℂ) * z) ≠ 0 :=
    hN (k + N) (by omega)
  have hTp (k : ℕ) : 0 < T k := zero_lt_one.trans_le (htail k).1
  have hTD (k : ℕ) (z : ℂ) (hz : z ∈ D) : (T k : ℂ) * z ∈ S :=
    (htail k).2.1 z (hDbig hz)
  have hUlim' : Tendsto (fun k => ∫ z in D, ‖ScalarAnalytic.potential v (T k) z - U z‖)
      atTop (𝓝 0) := hUlim.comp (tendsto_add_atTop_nat N)
  have hV : TendstoUniformlyOn
      (fun k => PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v) (T k))
      H atTop D := (hlim.mono hDbig).seq_tendstoUniformlyOn T hTt
  have hlu (k : ℕ) : IntegrableOn (ScalarAnalytic.potential v (T k)) D :=
    ScalarAnalytic.potential_integrableOn_compact hS hconn hv hz₀ hn₀ (hTp k).ne'
      (hTD k) Subset.rfl hDc
  have hHi : IntegrableOn H D := (hH.mono hDbig).integrableOn_compact hDc
  have hupper : ∀ᵐ z ∂volume.restrict D, U z ≤ H z := by
    apply ScalarL1Convergence.ae_le_of_L1_and_uniform_limits hDc.measurableSet hlu
      hUi hHi hUlim' hV
    apply Eventually.of_forall
    intro k
    exact ScalarAnalytic.potential_le_jet_ae hn hS hconn hv hz₀ hn₀ (hTp k)
      hDc.measurableSet (hTD k)
  have hlower : ∀ᵐ z ∂volume.restrict (interior D), H z ≤ U z :=
    ScalarL1Identification.jet_limit_le_scalar_L1_limit_ae hS hconn hv hz₀ hn₀ hDc
      (fun k => (htail k).1) hTt hTD hUi hUlim'
      (fun k z hz => (htail k).2.2 z (hDbig (interior_subset hz)))
      (fun z hz => hV.tendsto_at (interior_subset hz))
  have heq : U =ᵐ[volume.restrict K] H := by
    have hu := hupper.filter_mono (ae_mono (Measure.restrict_mono hKD le_rfl))
    have hl := hlower.filter_mono (ae_mono (Measure.restrict_mono hKint le_rfl))
    filter_upwards [hu, hl] with z hzu hzl
    exact le_antisymm hzu hzl
  have hsmalllim : Tendsto (fun k => ∫ z in K, ‖ScalarAnalytic.potential v (T k) z - U z‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg fun z => norm_nonneg _) _ hUlim'
    intro k
    exact setIntegral_mono_set ((hlu k).sub hUi).norm (ae_of_all _ fun z => norm_nonneg _)
      (ae_of_all _ fun z hz => hKD hz)
  exact ⟨τ, hτ, U, hsmalllim, heq⟩

/-- The full local output needed by the compact-cover step. Integrability is
only eventual on this disk; no assertion is made that a fixed finite scale
maps the entire unbounded phase cone into the analytic domain. -/
theorem actual_scalar_L1_on_closedBall {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {S : Set ℂ} {H : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hv : AnalyticOnNhd ℂ v S)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (10 * r), (R : ℂ) * z ∈ S)
    (hH : ContinuousOn H (closedBall c (10 * r)))
    (hlim : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop (closedBall c (10 * r)))
    (hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c (10 * r),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0) :
    (∀ᶠ R : ℝ in atTop, IntegrableOn
      (fun z => ‖ScalarAnalytic.potential v R z - H z‖) (closedBall c r)) ∧
    Tendsto (fun R : ℝ => ∫ z in closedBall c r,
      ‖ScalarAnalytic.potential v R z - H z‖) atTop (𝓝 0) := by
  refine ⟨?_, actual_scalar_L1_tendsto_on_closedBall hn hr hS hconn hv hDS hH hlim hjet⟩
  obtain ⟨T₀, hT₀S, hT₀jet⟩ := (hDS.and hjet).exists
  have hc : c ∈ closedBall c (10 * r) := mem_closedBall_self (by positivity)
  have hsmall : closedBall c r ⊆ closedBall c (10 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hHi : IntegrableOn H (closedBall c r) :=
    (hH.mono hsmall).integrableOn_compact (isCompact_closedBall c r)
  filter_upwards [hDS, eventually_gt_atTop (0 : ℝ)] with R hRD hR
  have hui := ScalarAnalytic.potential_integrableOn_compact hS hconn hv (hT₀S c hc)
    (hT₀jet c hc) hR.ne' hRD hsmall (isCompact_closedBall c r)
  exact (hui.sub hHi).norm

#print axioms actual_scalar_L1_tendsto_on_closedBall
#print axioms actual_scalar_L1_on_closedBall
end V10.ScalarL1LocalLimit
