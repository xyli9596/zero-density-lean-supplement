import V10.ScalarCompactnessRemainder
import V10.HarmonicL1Compactness
import V10.ScalarCompactnessMovingCenter

/-!
# Local L¹ compactness of actual normalized analytic logarithms

The logarithmic divisor potentials are compact in L¹, and the actual harmonic
remainders are compact uniformly on smaller disks. This file combines these
two proved compactness mechanisms; subsequential L¹ convergence is a conclusion.
-/

noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology

namespace V10.ScalarCompactnessAssembly
open ScalarCompactnessLogPotential ScalarCompactnessJensen ScalarCompactnessDivisor
open ScalarCompactnessRemainder ScalarCompactnessL1Bounds ScalarCompactnessMovingCenter

theorem lp_restricted_integral_tendsto {P : ℕ → L1} {p : L1} (K : Set ℂ)
    (hP : Tendsto P atTop (𝓝 p)) :
    Tendsto (fun n => ∫ z in K, ‖P n z - p z‖) atTop (𝓝 0) := by
  have hb : ∀ n, (∫ z in K, ‖P n z - p z‖) ≤ dist (P n) p := by
    intro n
    rw [MeasureTheory.L1.dist_eq_integral_dist]
    simp only [dist_eq_norm]
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => norm_nonneg _) ((MeasureTheory.L1.integrable_coeFn _).sub
        (MeasureTheory.L1.integrable_coeFn _)).norm
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hb
  simpa only [dist_self] using hP.dist (tendsto_const_nhds (x := p))

theorem uniform_integral_tendsto {h : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hc : ∀ n, ContinuousOn (h n) K) (gc : ContinuousOn g K)
    (ht : TendstoUniformlyOn h g atTop K) :
    Tendsto (fun n => ∫ z in K, ‖h n z - g z‖) atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (volume.real K + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp ht) η hη] with n hn
  have hi : IntegrableOn (fun z => h n z - g z) K :=
    ((hc n).sub gc).integrableOn_compact hK
  have hb : (∫ z in K, ‖h n z - g z‖) ≤ volume.real K * η := by
    have hu : ∀ᵐ z ∂volume.restrict K, ‖h n z - g z‖ ≤ η := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      simpa only [dist_eq_norm, norm_sub_rev] using (hn z hz).le
    have h := integral_mono_ae hi.norm (integrable_const η) hu
    simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] using h
  have hm : 0 ≤ volume.real K := measureReal_nonneg
  have he : volume.real K * η < ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < volume.real K + 1)).mpr
    nlinarith
  have hnn : 0 ≤ ∫ z in K, ‖h n z - g z‖ := integral_nonneg fun _ => norm_nonneg _
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    using hb.trans_lt he

/-- Analytic input with explicit L¹ and divisor-mass bounds. Both bounds have
already been derived from moving-center norm bounds in the next theorem. -/
theorem analytic_log_tendsto_subseq_of_bounds
    {f : ℕ → ℂ → ℂ} {q : ℕ → ℝ} {c : ℂ} {r R L M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hq : ∀ n, 0 < q n) (hM : 0 < M)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnz : ∀ n, ∃ w ∈ closedBall c R, f n w ≠ 0)
    (hlog : ∀ n, (∫ z in closedBall c R, |Real.log ‖f n z‖ / q n|) ≤ L)
    (hmass : ∀ n, ∑ u ∈ divisorSupport (f n) c R,
      (MeromorphicOn.divisor (f n) (closedBall c R) u : ℝ) / q n ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ H : ℂ → ℝ,
      IntegrableOn H (closedBall c r) ∧
      Tendsto (fun n => ∫ z in closedBall c r,
        ‖Real.log ‖f (σ n) z‖ / q (σ n) - H z‖) atTop (𝓝 0) := by
  have hR : 0 < R := hr.trans_lt hrR
  have he : ∀ n, ∃ h : ℂ → ℝ, HarmonicOnNhd h (closedBall c R) ∧
      (fun z => Real.log ‖f n z‖ / q n) =ᵐ[volume.restrict (closedBall c R)]
        (fun z => divisorPotential (f n) c R (q n) (3 * R) z + h z) ∧
      (∫ z in closedBall c R, ‖h z‖) ≤ L + M * ‖cutoffLogL1 (3 * R)‖ := by
    intro n
    obtain ⟨w, hw, hfw⟩ := hnz n
    obtain ⟨h, hh, he, hb⟩ := exists_harmonic_remainder hR (hq n) hw (hf n) hfw
    refine ⟨h, hh, he, hb.trans (add_le_add (hlog n) ?_)⟩
    exact (norm_divisorPotential_le (hq n) (hf n)).trans
      (mul_le_mul_of_nonneg_right (hmass n) (norm_nonneg _))
  choose h hh he hb using he
  obtain ⟨p, σ, hσ, hP⟩ := divisor_potential_tendsto_subseq_of_mass_bound
    (cutoff := 3 * R) hq hM hf hmass
  obtain ⟨τ, hτ, g, hgc, hG⟩ := HarmonicL1Compactness.harmonic_L1_uniform_subsequence
    hr hrR (fun n => hh (σ n)) (fun n => hb (σ n))
  let H : ℂ → ℝ := fun z => p z + g z
  have hip : IntegrableOn (p : ℂ → ℝ) (closedBall c r) :=
    (MeasureTheory.L1.integrable_coeFn p).mono_measure Measure.restrict_le_self
  have hig : IntegrableOn g (closedBall c r) := hgc.integrableOn_compact (isCompact_closedBall c r)
  refine ⟨σ ∘ τ, hσ.comp hτ, H, hip.add hig, ?_⟩
  have hp0 := lp_restricted_integral_tendsto (closedBall c r) (hP.comp hτ.tendsto_atTop)
  have hg0 := uniform_integral_tendsto (isCompact_closedBall c r)
    (fun n => (hh (σ (τ n))).continuousOn.mono (closedBall_subset_closedBall hrR.le)) hgc hG
  have hnonneg : ∀ n, 0 ≤ (∫ z in closedBall c r,
      ‖Real.log ‖f ((σ ∘ τ) n) z‖ / q ((σ ∘ τ) n) - H z‖) :=
    fun _ => integral_nonneg fun _ => norm_nonneg _
  apply squeeze_zero hnonneg _ (by simpa only [zero_add] using hp0.add hg0)
  intro n
  obtain ⟨w, hw, hfw⟩ := hnz (σ (τ n))
  have hib : IntegrableOn (fun z => Real.log ‖f (σ (τ n)) z‖ / q (σ (τ n)))
      (closedBall c R) := (log_inputs_on_disk_of_point hw (hf (σ (τ n))) hfw).1.div_const
        (q (σ (τ n)))
  have hi := hib.mono_set (closedBall_subset_closedBall hrR.le)
  have hipn : IntegrableOn
      (divisorPotential (f (σ (τ n))) c R (q (σ (τ n))) (3 * R) : ℂ → ℝ)
      (closedBall c r) := (MeasureTheory.L1.integrable_coeFn _).mono_measure Measure.restrict_le_self
  have hih : IntegrableOn (h (σ (τ n))) (closedBall c r) :=
    ((hh (σ (τ n))).continuousOn.mono (closedBall_subset_closedBall hrR.le)).integrableOn_compact
      (isCompact_closedBall c r)
  have he' := (he (σ (τ n))).filter_mono
    (ae_mono (Measure.restrict_mono (closedBall_subset_closedBall hrR.le) le_rfl))
  have htri : ∀ᵐ z ∂volume.restrict (closedBall c r),
      ‖Real.log ‖f (σ (τ n)) z‖ / q (σ (τ n)) - H z‖ ≤
        ‖divisorPotential (f (σ (τ n))) c R (q (σ (τ n))) (3 * R) z - p z‖ +
        ‖h (σ (τ n)) z - g z‖ := by
    filter_upwards [he'] with z hz
    rw [hz]
    dsimp [H]
    have hid : divisorPotential (f (σ (τ n))) c R (q (σ (τ n))) (3 * R) z +
        h (σ (τ n)) z - (p z + g z) =
        (divisorPotential (f (σ (τ n))) c R (q (σ (τ n))) (3 * R) z - p z) +
          (h (σ (τ n)) z - g z) := by ring
    rw [hid]
    exact norm_add_le
      (divisorPotential (f (σ (τ n))) c R (q (σ (τ n))) (3 * R) z - p z)
      (h (σ (τ n)) z - g z)
  have hbound := integral_mono_ae (hi.sub (hip.add hig)).norm
    ((hipn.sub hip).norm.add (hih.sub hig).norm) htri
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  have hadd := integral_add (hipn.sub hip).norm (hih.sub hig).norm
  simp only [Pi.sub_apply] at hadd
  rw [hadd] at hbound
  simpa only [Function.comp_def] using hbound

/-- Actual scalar logarithms have an L¹-convergent subsequence on a common
inner disk. Only analyticity, a uniform normalized norm upper bound, and a
moving lower sample are assumed. In particular neither compactness, a divisor
mass estimate, nor a harmonic-remainder bound is assumed. -/
theorem analytic_log_L1_subsequence_moving_center
    {f : ℕ → ℂ → ℂ} {q : ℕ → ℝ} {c : ℂ} {r B C : ℝ}
    (hr : 0 < r) (hq : ∀ n, 0 < q n) (hB : 0 ≤ B)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c (5 * r)))
    (hupper : ∀ n z, z ∈ closedBall c (5 * r) → ‖f n z‖ ≤ Real.exp (q n * B))
    (hsample : ∀ n, ∃ a ∈ closedBall c r, Real.exp (-q n * C) ≤ ‖f n a‖) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ H : ℂ → ℝ,
      IntegrableOn H (closedBall c r) ∧
      Tendsto (fun n => ∫ z in closedBall c r,
        ‖Real.log ‖f (σ n) z‖ / q (σ n) - H z‖) atTop (𝓝 0) := by
  choose a ha hlower using hsample
  let M : ℝ := 1 + max 0 ((B + C) / Real.log (4 / 3 : ℝ))
  apply analytic_log_tendsto_subseq_of_bounds (R := 2 * r) hr.le (by linarith) hq
    (show 0 < M by dsimp [M]; positivity)
    (fun n => (hf n).mono (closedBall_subset_closedBall (by linarith)))
  · intro n
    exact ⟨a n, closedBall_subset_closedBall (by linarith) (ha n),
      norm_pos_iff.mp ((Real.exp_pos _).trans_le (hlower n))⟩
  · exact fun n => moving_center_log_L1_bound hr (hq n) hB (ha n) (hf n) (hupper n) (hlower n)
  · intro n
    have hm := moving_center_divisor_mass_le hr (hq n) hB (ha n) (hf n) (hupper n) (hlower n)
    rw [divisor_sum_eq, Int.cast_sum, Finset.sum_div] at hm
    exact hm.trans (by dsimp [M]; linarith [le_max_right 0 ((B + C) / Real.log (4 / 3 : ℝ))])

end V10.ScalarCompactnessAssembly
