import V10.HolomorphicProjectionAverage
import V10.LogHomogeneousPluriSeries

/-!
# Genuine extended deficits of averaged holomorphic projections

The real integral away from zero is identified with a nonnegative extended
parameter integral. At the zero coefficient the latter is genuinely infinite.
Consequently the punctured deficits used in the exceptional-cone series carry
actual lower semicontinuity and complex-line disk supermean data.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace V10.ProjectionAverageDeficit
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open HolomorphicProjectionAverage ProjectionPlurisubharmonic PluriPotentialIntegral
open PluriPotentialSeries LogHomogeneousPluriSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def normalizedProjection (F : ℂ → E →L[ℂ] ℂ) (z : ℂ) : E →L[ℂ] ℂ :=
  (‖F z‖⁻¹ : ℝ) • F z

def averagedDeficit (F : ℂ → E →L[ℂ] ℂ) (φ : ℂ → ℝ) (M : ℝ) (c : E) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (φ z) * logDeficit (normalizedProjection F z) M c

theorem normalizedProjection_norm (F : ℂ → E →L[ℂ] ℂ) (z : ℂ) (c : E) :
    ‖normalizedProjection F z c‖ = ‖F z c‖ / ‖F z‖ := by
  simp only [normalizedProjection, _root_.smul_apply, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_norm, div_eq_mul_inv, mul_comm]

theorem normalizedProjection_bound {F : ℂ → E →L[ℂ] ℂ} (hFn : ∀ z, F z ≠ 0)
    (z : ℂ) (c : E) : ‖normalizedProjection F z c‖ ≤ ‖c‖ := by
  rw [normalizedProjection_norm]
  apply (div_le_iff₀ (norm_pos_iff.mpr (hFn z))).mpr
  simpa only [mul_comm] using (F z).le_opNorm c

theorem normalizedProjection_continuous {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) : Continuous (normalizedProjection F) :=
  (hF.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (hFn z))).smul hF

/-- The actual logarithmic deficit equals the finite real average deficit
away from the zero coefficient. The exceptional projection zeros are proved
null by entire analyticity and nontriviality. -/
theorem averagedDeficit_eq_ofReal {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {M : ℝ} (hcM : ‖c‖ ≤ Real.exp M) :
    averagedDeficit F φ M c =
      ENNReal.ofReal (M * (∫ z, φ z) - averagedLogProjection F φ c) := by
  have hφi : Integrable φ volume := hφ.integrable_of_hasCompactSupport hφc
  have hlogi := weighted_logProjection_integrable hF hFn ha hn hφ hφc
  have hi : Integrable (fun z => φ z * (M - logProjection F c z)) volume := by
    convert (hφi.const_mul M).sub hlogi using 1
    ext z
    simp only [Pi.sub_apply]
    ring
  have hnz := ae_ne_zero_of_entire ha hn
  have hnonneg : 0 ≤ᵐ[volume] (fun z => φ z * (M - logProjection F c z)) := by
    filter_upwards [hnz] with z hz
    apply mul_nonneg (hφn z) (sub_nonneg.mpr ?_)
    have hp : 0 < ‖F z c‖ / ‖F z‖ :=
      div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr (hFn z))
    have hb : ‖F z c‖ / ‖F z‖ ≤ Real.exp M :=
      (normalizedProjection_norm F z c ▸ normalizedProjection_bound hFn z c).trans hcM
    simpa only [logProjection, Real.log_exp] using Real.log_le_log hp hb
  have he : (fun z => ENNReal.ofReal (φ z) * logDeficit (normalizedProjection F z) M c)
      =ᵐ[volume] (fun z => ENNReal.ofReal (φ z * (M - logProjection F c z))) := by
    filter_upwards [hnz] with z hz
    have hnorm : normalizedProjection F z c ≠ 0 := by
      apply norm_pos_iff.mp
      rw [normalizedProjection_norm]
      exact div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr (hFn z))
    simp only [logDeficit, if_neg hnorm, normalizedProjection_norm, logProjection,
      ENNReal.ofReal_mul (hφn z)]
  rw [averagedDeficit, lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  congr 1
  have heq : (fun z => φ z * (M - logProjection F c z)) =
      (fun z => M * φ z - φ z * logProjection F c z) := by ext z; ring
  rw [heq, integral_sub (hφi.const_mul M) hlogi, integral_const_mul]
  rfl

/-- A positive total weight makes zero a genuine infinite deficit. -/
theorem averagedDeficit_zero {F : ℂ → E →L[ℂ] ℂ} {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφn : ∀ z, 0 ≤ φ z)
    (hφpos : 0 < ∫ z, φ z) (M : ℝ) : averagedDeficit F φ M 0 = ∞ := by
  simp only [averagedDeficit, logDeficit, map_zero, if_pos]
  rw [lintegral_mul_const (f := fun z : ℂ => ENNReal.ofReal (φ z)) ∞
      (ENNReal.continuous_ofReal.measurable.comp hφ.measurable),
    ← ofReal_integral_eq_lintegral_ofReal (hφ.integrable_of_hasCompactSupport hφc)
      (ae_of_all _ hφn)]
  exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hφpos))

/-- Genuine plurisuperharmonic data are local in the coefficient domain. -/
theorem plurisuperharmonic_congr {f g : E → ℝ≥0∞} {U : Set E}
    (hU : IsOpen U) (hf : PlurisuperharmonicOn f U) (he : EqOn f g U) :
    PlurisuperharmonicOn g U := by
  refine ⟨?_, ?_⟩
  · intro c hc
    apply LowerSemicontinuousWithinAt.congr_of_eventuallyEq
      (hf.lowerSemicontinuousOn c hc) hc
    exact eventually_mem_nhdsWithin.mono (fun x hx => he hx)
  · intro a b
    have hS : IsOpen {z : ℂ | a + z • b ∈ U} :=
      hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hline := hf.onLine a b
    refine ⟨hline.aemeasurable.congr
      (ae_restrict_of_forall_mem hS.measurableSet (fun z hz => he hz)), ?_⟩
    intro c r hr hsub
    have hI : (∫⁻ z in closedBall c r, g (a + z • b)) =
        ∫⁻ z in closedBall c r, f (a + z • b) := by
      apply lintegral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_closedBall
        (fun z hz => (he (hsub hz)).symm)
    rw [hI, ← he (hsub (mem_closedBall_self hr.le))]
    exact hline.supermean c r hr hsub

section Pluri
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The extended averaged deficit itself has actual lower semicontinuity and
complex-line supermeans. The weight is incorporated into a positive measure. -/
theorem averagedDeficit_plurisuperharmonic {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {φ : ℂ → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : 0 ≤ M) :
    PlurisuperharmonicOn (averagedDeficit F φ M) (ball (0 : E) (Real.exp M)) := by
  have hNF := normalizedProjection_continuous hF hFn
  have hdensity : Measurable (fun z : ℂ => ENNReal.ofReal (φ z)) :=
    ENNReal.continuous_ofReal.measurable.comp hφ.measurable
  have he : (fun c => ∫⁻ z, logDeficit (normalizedProjection F z) M c
      ∂volume.withDensity (fun z => ENNReal.ofReal (φ z))) = averagedDeficit F φ M := by
    funext c
    have hev : Measurable (fun z : ℂ => normalizedProjection F z c) :=
      (hNF.clm_apply continuous_const).measurable
    have hm : Measurable (fun z : ℂ => logDeficit (normalizedProjection F z) M c) := by
      unfold logDeficit
      apply Measurable.ite (measurableSet_eq_fun hev measurable_const) measurable_const
      exact ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub hev.norm.log)
    exact lintegral_withDensity_eq_lintegral_mul volume hdensity hm
  rw [← he]
  apply integrated_logDeficit_of_continuous _ isOpen_ball hM _ hNF
  intro z c hc
  exact (normalizedProjection_bound hFn z c).trans (mem_ball_zero_iff.mp hc).le

/-- The true punctured real-average deficit agrees with the extended parameter
integral on the coefficient ball, including its infinite value at the origin. -/
theorem punctured_average_plurisuperharmonic {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) (hφpos : 0 < ∫ z, φ z)
    {M : ℝ} (hM : 0 ≤ M) :
    PlurisuperharmonicOn
      (fun c => if c = 0 then ∞ else
        ENNReal.ofReal (M * (∫ z, φ z) - averagedLogProjection F φ c))
      (ball (0 : E) (Real.exp M)) := by
  classical
  apply plurisuperharmonic_congr isOpen_ball (averagedDeficit_plurisuperharmonic hF hFn hφ hM)
  intro c hc
  dsimp only
  by_cases hz : c = 0
  · subst c
    simp only [if_pos, averagedDeficit_zero hφ hφc hφn hφpos]
  · rw [if_neg hz]
    exact averagedDeficit_eq_ofReal hF hFn (ha c hz) (hn c hz) hφ hφc hφn
      (mem_ball_zero_iff.mp hc).le

/-- Family-indexed form consumed by the exceptional-cone series. The summand
is the actual holomorphic average and its upper bound is its weight mass times
`log B`; neither the deficit identity nor plurisuperharmonicity is a premise. -/
theorem puncturedDeficit_on_ball {F : ℕ → ℂ → E →L[ℂ] ℂ} {φ : ℕ → ℂ → ℝ}
    (j : ℕ) (B : ℝ) (hB : 1 < B)
    (hF : Continuous (F j)) (hFn : ∀ z, F j z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F j z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F j z c ≠ 0)
    (hφ : Continuous (φ j)) (hφc : HasCompactSupport (φ j))
    (hφn : ∀ z, 0 ≤ φ j z) (hφpos : 0 < ∫ z, φ j z) :
    PlurisuperharmonicOn
      (puncturedDeficit (fun i => averagedLogProjection (F i) (φ i))
        (fun i => (∫ z, φ i z) * Real.log B) j) (ball (0 : E) B) := by
  have hp := punctured_average_plurisuperharmonic hF hFn ha hn hφ hφc hφn hφpos
    (Real.log_nonneg hB.le)
  change PlurisuperharmonicOn (fun c => if c = 0 then ∞ else
    ENNReal.ofReal ((∫ z, φ j z) * Real.log B - averagedLogProjection (F j) (φ j) c)) _
  simpa only [Real.exp_log (zero_lt_one.trans hB), mul_comm] using hp
end Pluri

#print axioms averagedDeficit_eq_ofReal
#print axioms averagedDeficit_zero
#print axioms averagedDeficit_plurisuperharmonic
#print axioms puncturedDeficit_on_ball
end V10.ProjectionAverageDeficit
