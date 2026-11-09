import V10.ProjectionGaussianFamily
import V10.PluriPotentialIntegral
import Mathlib.Tactic

/-! Actual Gaussian finiteness of the logarithmic deficit potential series.
The only summability premise is the weighted mass of the physical-parameter
measures. Every logarithmic Gaussian bound is derived from actual normalized
complex projections, including their infinite values on kernels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology NNReal ENNReal
namespace V10.ProjectionDeficitGaussian
open ProjectionGaussian ProjectionGaussianLoss ProjectionPlurisubharmonic
open PluriPotentialSeries PluriPotentialIntegral
set_option backward.isDefEq.respectTransparency false

variable {Z E : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The actual logarithmic deficit is controlled by the actual absolute
logarithmic loss. At zeros both extended quantities are infinite. -/
theorem normalized_logDeficit_le (F : E →L[ℂ] ℂ) (hF : F ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) (c : E) :
    logDeficit (normalized F) M c ≤ ENNReal.ofReal M + loss F c := by
  by_cases hc : F c = 0
  · simp [loss, hc]
  have hnc : normalized F c ≠ 0 := by
    simp only [normalized, smul_apply, smul_eq_mul, mul_ne_zero_iff]
    exact ⟨inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hF)), hc⟩
  rw [logDeficit, if_neg hnc, loss, if_neg hc, normalized_apply_norm,
    ← ENNReal.ofReal_add hM (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  linarith [neg_le_abs (Real.log (‖F c‖ / ‖F‖))]

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z] in
theorem continuous_normalized {F : Z → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) : Continuous (fun z => normalized (F z)) := by
  exact ((Complex.continuous_ofReal.comp hF.norm).inv₀
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hFn z)))).smul hF

def deficitAverage (σ : Measure Z) (F : Z → E →L[ℂ] ℂ) (M : ℝ) (c : E) : ℝ≥0∞ :=
  ∫⁻ z, logDeficit (normalized (F z)) M c ∂σ

omit [SecondCountableTopology Z] [IsScalarTower ℝ ℂ E] in
theorem measurable_deficitAverage {σ : Measure Z} [SFinite σ]
    {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) (M : ℝ) :
    Measurable (deficitAverage σ F M) := by
  apply Measurable.lintegral_prod_left
  change Measurable (fun p : Z × E => logDeficit (normalized (F p.1)) M p.2)
  apply measurable_logDeficit (F := fun z => normalized (F z))
  exact (((continuous_normalized hF hFn).comp continuous_fst).clm_apply continuous_snd).measurable

omit [SecondCountableTopology Z] in
/-- A finite universal constant bounds the Gaussian integral of the actual
deficit average, with no assumed logarithmic integral estimate. -/
theorem lintegral_deficitAverage_le {σ : Measure Z} [SFinite σ]
    {F : Z → E →L[ℂ] ℂ} (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    (∫⁻ c, deficitAverage σ F M c ∂complexGaussian E) ≤
      (ENNReal.ofReal M + ENNReal.ofReal gaussianLogConstant) * σ univ := by
  have hm : Measurable (fun p : Z × E => logDeficit (normalized (F p.1)) M p.2) :=
    measurable_logDeficit (F := fun z => normalized (F z)) M
      (((continuous_normalized hF hFn).comp continuous_fst).clm_apply continuous_snd).measurable
  unfold deficitAverage
  rw [lintegral_lintegral_swap (f := fun c z => logDeficit (normalized (F z)) M c)
    (hm.comp measurable_swap).aemeasurable]
  calc
    _ ≤ ∫⁻ z, ∫⁻ c, ENNReal.ofReal M + loss (F z) c ∂complexGaussian E ∂σ :=
      lintegral_mono fun z => lintegral_mono fun c => normalized_logDeficit_le (F z) (hFn z) hM c
    _ = (ENNReal.ofReal M + ENNReal.ofReal gaussianLogConstant) * σ univ := by
      simp_rw [lintegral_add_left measurable_const, lintegral_loss _ (hFn _)]
      simp [add_mul]

/-- The weighted series uses the actual physical-parameter measures σ_m.
For the manuscript their masses incorporate the cutoff masses, and the
weights incorporate the factors b_L / Q_m after enumeration. -/
def deficitSeries (σ : ℕ → Measure Z) (F : ℕ → Z → E →L[ℂ] ℂ)
    (w : ℕ → ℝ≥0) (M : ℝ) (c : E) : ℝ≥0∞ :=
  ∑' m, (w m : ℝ≥0∞) * deficitAverage (σ m) (F m) M c

omit [SecondCountableTopology Z] [IsScalarTower ℝ ℂ E] in
theorem measurable_deficitSeries {σ : ℕ → Measure Z} [∀ m, SFinite (σ m)]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0) (w : ℕ → ℝ≥0) (M : ℝ) :
    Measurable (deficitSeries σ F w M) :=
  Measurable.tsum fun m => (measurable_deficitAverage (hF m) (hFn m) M).const_mul _

omit [SecondCountableTopology Z] in
theorem lintegral_deficitSeries_le {σ : ℕ → Measure Z} [∀ m, SFinite (σ m)]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0) (w : ℕ → ℝ≥0) {M : ℝ} (hM : 0 ≤ M) :
    (∫⁻ c, deficitSeries σ F w M c ∂complexGaussian E) ≤
      (ENNReal.ofReal M + ENNReal.ofReal gaussianLogConstant) *
        ∑' m, (w m : ℝ≥0∞) * σ m univ := by
  unfold deficitSeries
  rw [lintegral_tsum (fun m =>
    ((measurable_deficitAverage (hF m) (hFn m) M).const_mul _).aemeasurable)]
  simp_rw [lintegral_const_mul'' _ (measurable_deficitAverage (hF _) (hFn _) M).aemeasurable]
  calc
    _ ≤ ∑' m, (w m : ℝ≥0∞) *
        ((ENNReal.ofReal M + ENNReal.ofReal gaussianLogConstant) * σ m univ) :=
      ENNReal.tsum_le_tsum fun m => mul_le_mul_right
        (lintegral_deficitAverage_le (hF m) (hFn m) hM) _
    _ = _ := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      ext m
      exact mul_left_comm _ _ _

omit [SecondCountableTopology Z] in
/-- Summable physical masses imply Gaussian-a.e. finiteness of the actual
extended deficit series. No Gaussian logarithmic bound is an input. -/
theorem ae_deficitSeries_ne_top {σ : ℕ → Measure Z} [∀ m, SFinite (σ m)]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0) (w : ℕ → ℝ≥0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : (∑' m, (w m : ℝ≥0∞) * σ m univ) ≠ ∞) :
    ∀ᵐ c ∂complexGaussian E, deficitSeries σ F w M c ≠ ∞ := by
  have hi : (∫⁻ c, deficitSeries σ F w M c ∂complexGaussian E) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hmass)
      (lintegral_deficitSeries_le hF hFn w hM)
  exact (ae_lt_top' (measurable_deficitSeries hF hFn w M).aemeasurable hi).mono fun _ h => h.ne

omit [SecondCountableTopology Z] in
/-- Every coefficient ball has a point where the actual negative potential
is finite. Thus the potential is not identically minus infinity on any ball. -/
theorem exists_finite_potential_in_ball {σ : ℕ → Measure Z} [∀ m, SFinite (σ m)]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0) (w : ℕ → ℝ≥0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : (∑' m, (w m : ℝ≥0∞) * σ m univ) ≠ ∞)
    (a : E) {r : ℝ} (hr : 0 < r) :
    ∃ c ∈ ball a r, negativePotential (deficitSeries σ F w M) c ≠ ⊥ := by
  obtain ⟨c, hc, hfinite⟩ := ProjectionGaussianSupport.exists_good_in_ball
    (ae_deficitSeries_ne_top hF hFn w hM hmass) a hr
  exact ⟨c, hc, (negativePotential_eq_bot _ _).not.mpr hfinite⟩

omit [IsScalarTower ℝ ℂ E] in
/-- The same actual series has lower semicontinuity and genuine complex-line
supermean inequalities on its coefficient ball. The projection bound follows
from the proved unit operator norm of normalized F. -/
theorem deficitSeries_plurisuperharmonic {σ : ℕ → Measure Z} [∀ m, SFinite (σ m)]
    {F : ℕ → Z → E →L[ℂ] ℂ} (hF : ∀ m, Continuous (F m))
    (hFn : ∀ m z, F m z ≠ 0) (w : ℕ → ℝ≥0) {M : ℝ} (hM : 0 ≤ M) :
    PlurisuperharmonicOn (deficitSeries σ F w M) (ball 0 (Real.exp M)) := by
  apply PlurisuperharmonicOn.tsum
  intro m
  have hp := integrated_logDeficit_of_continuous
    ((w m : ℝ≥0∞) • σ m) isOpen_ball hM
    (F := fun z => normalized (F m z))
    (U := ball (0 : E) (Real.exp M))
    (by
      intro z c hc
      have h := (normalized (F m z)).le_opNorm c
      rw [normalized_norm _ (hFn m z), one_mul] at h
      exact h.trans (mem_ball_zero_iff.mp hc).le)
    (continuous_normalized (hF m) (hFn m))
  simpa only [lintegral_smul_measure, smul_eq_mul, deficitAverage] using hp

#print axioms normalized_logDeficit_le
#print axioms lintegral_deficitSeries_le
#print axioms ae_deficitSeries_ne_top
#print axioms exists_finite_potential_in_ball
#print axioms deficitSeries_plurisuperharmonic
end V10.ProjectionDeficitGaussian
