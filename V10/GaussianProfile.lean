import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Prod

/-!
# The parabolic change of variables in the global limiting profile

This module concerns the explicit candidate limiting measure only. It does not
assert convergence of zero measures or genericity of initial values.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace V10.GaussianProfile
noncomputable section

/-- The parabolic change `(ξ,η) ↦ (u,τ) = (-ξ-η²/2,η)`. -/
def parabolic (p : ℝ × ℝ) : ℝ × ℝ := (-p.1 - p.2 ^ 2 / 2, p.2)

@[simp] theorem parabolic_involutive (p : ℝ × ℝ) : parabolic (parabolic p) = p := by
  ext <;> simp [parabolic]

@[fun_prop] theorem continuous_parabolic : Continuous parabolic := by
  unfold parabolic
  fun_prop

@[fun_prop] theorem measurable_parabolic : Measurable parabolic := continuous_parabolic.measurable

/-- The disk limit domain, bounded by a parabola. -/
def parabolicDomain : Set (ℝ × ℝ) := {p | p.1 ≤ -p.2 ^ 2 / 2}

/-- The coordinate change takes the parabolic domain to the radial half-plane. -/
theorem mem_domain_iff (p : ℝ × ℝ) : p ∈ parabolicDomain ↔ 0 ≤ (parabolic p).1 := by
  simp only [parabolicDomain, mem_ofPred_eq, parabolic]
  constructor <;> intro h <;> linarith

@[simp] theorem parabolic_mem_domain_iff (p : ℝ × ℝ) :
    parabolic p ∈ parabolicDomain ↔ 0 ≤ p.1 := by
  rw [mem_domain_iff, parabolic_involutive]

/-- Volume preservation is proved by a skew product of one-dimensional
translations/reflections, avoiding an assumed Jacobian identity. -/
theorem measurePreserving_parabolic : MeasurePreserving parabolic volume volume := by
  change MeasurePreserving parabolic ((volume : Measure ℝ).prod volume)
    ((volume : Measure ℝ).prod volume)
  have hskew : MeasurePreserving (fun p : ℝ × ℝ ↦ (p.1, -p.2 - p.1 ^ 2 / 2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun y x : ℝ ↦ -x - y ^ 2 / 2) (by fun_prop)
    apply Filter.Eventually.of_forall
    intro y
    have h := (measurePreserving_add_right (volume : Measure ℝ) (-(y ^ 2 / 2))).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    simpa only [Function.comp_def, sub_eq_add_neg] using h.map_eq
  have h := measurePreserving_swap.comp (hskew.comp measurePreserving_swap)
  convert h using 1; rfl

/-- The total mass constant in the paper. -/
def massConstant (P : ℝ) : ℝ := P / (2 * Real.pi * Real.sqrt (2 * Real.pi))

lemma massConstant_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ massConstant P := by
  unfold massConstant
  positivity

/-- The pointwise Gaussian factorization, including the exact pi constant. -/
theorem density_factorization (P u τ : ℝ) :
    P / (4 * Real.pi ^ 2) * Real.exp (-u - τ ^ 2 / 2) =
      massConstant P * Real.exp (-u) * gaussianPDFReal 0 1 τ := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [show -u - τ ^ 2 / 2 = -u + -(τ ^ 2 / 2) by ring, Real.exp_add]
  simp only [massConstant, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have he : Real.exp (-(τ ^ 2 / 2)) = Real.exp (-τ ^ 2 / 2) := by congr 1; ring
  rw [he]
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- The probability density of independent Exp(1) and N(0,1) coordinates. -/
def productDensity (p : ℝ × ℝ) : ℝ≥0∞ :=
  exponentialPDF 1 p.1 * gaussianPDF 0 1 p.2

@[fun_prop] lemma measurable_productDensity : Measurable productDensity := by
  unfold productDensity exponentialPDF
  fun_prop

/-- The mass-weighted radial-angular density. -/
def targetDensity (P : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (massConstant P) * productDensity p

@[fun_prop] lemma measurable_targetDensity (P : ℝ) : Measurable (targetDensity P) := by
  unfold targetDensity
  fun_prop

/-- The density in the original parabolic coordinates. -/
def sourceDensity (P : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ := by
  classical
  exact if p ∈ parabolicDomain then ENNReal.ofReal (P / (4 * Real.pi ^ 2) * Real.exp p.1) else 0

/-- Exact density transformation; the domain cutoff becomes `u ≥ 0`. -/
theorem sourceDensity_parabolic {P : ℝ} (hP : 0 ≤ P) (p : ℝ × ℝ) :
    sourceDensity P (parabolic p) = targetDensity P p := by
  by_cases hp : 0 ≤ p.1
  · rw [sourceDensity, if_pos ((parabolic_mem_domain_iff p).mpr hp)]
    simp only [parabolic, targetDensity, productDensity, exponentialPDF_of_nonneg hp,
      one_mul, gaussianPDF]
    rw [density_factorization]
    rw [ENNReal.ofReal_mul (mul_nonneg (massConstant_nonneg hP) (Real.exp_pos _).le),
      ENNReal.ofReal_mul (massConstant_nonneg hP)]
    rw [mul_assoc]
  · have hn : p.1 < 0 := lt_of_not_ge hp
    rw [sourceDensity, if_neg ((parabolic_mem_domain_iff p).not.mpr hp)]
    simp [targetDensity, productDensity, exponentialPDF_of_neg hn]

/-- The explicit candidate measure really pushes forward to the product-form
radial-angular density. This is a measure equality, not only a formal Jacobian. -/
theorem map_sourceDensity {P : ℝ} (hP : 0 ≤ P) :
    Measure.map parabolic (volume.withDensity (sourceDensity P)) =
      volume.withDensity (targetDensity P) := by
  ext s hs
  rw [Measure.map_apply measurable_parabolic hs,
    withDensity_apply _ (measurable_parabolic hs), withDensity_apply _ hs]
  have hpoint : ∀ p, sourceDensity P p = targetDensity P (parabolic p) := by
    intro p
    simpa only [parabolic_involutive] using sourceDensity_parabolic hP (parabolic p)
  simp_rw [hpoint]
  exact measurePreserving_parabolic.setLIntegral_comp_preimage hs (measurable_targetDensity P)

/-- The two factors are normalized, hence their product is a probability density. -/
theorem lintegral_productDensity : ∫⁻ p, productDensity p = 1 := by
  change (∫⁻ p, exponentialPDF 1 p.1 * gaussianPDF 0 1 p.2
    ∂(volume : Measure ℝ).prod volume) = 1
  rw [lintegral_prod_mul (by unfold exponentialPDF; fun_prop) (by fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num), lintegral_gaussianPDF_eq_one 0 (by norm_num)]
  simp

/-- Exact total mass of the target model. -/
theorem lintegral_targetDensity (P : ℝ) :
    ∫⁻ p, targetDensity P p = ENNReal.ofReal (massConstant P) := by
  unfold targetDensity
  rw [lintegral_const_mul _ measurable_productDensity, lintegral_productDensity, mul_one]

/-- Exact total mass of the original parabolic model. -/
theorem sourceDensity_total_mass {P : ℝ} (hP : 0 ≤ P) :
    (volume.withDensity (sourceDensity P)) Set.univ = ENNReal.ofReal (massConstant P) := by
  have h := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ Set.univ) (map_sourceDensity hP)
  rw [Measure.map_apply measurable_parabolic MeasurableSet.univ] at h
  simpa only [preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_targetDensity] using h

/-- The product probability law corresponding to the two limiting coordinates. -/
def modelMeasure : Measure (ℝ × ℝ) := (expMeasure 1).prod (gaussianReal 0 1)

theorem modelMeasure_isProbability : IsProbabilityMeasure modelMeasure := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  unfold modelMeasure
  infer_instance

/-- The product density agrees with the actual named probability distributions. -/
theorem withDensity_productDensity : volume.withDensity productDensity = modelMeasure := by
  unfold modelMeasure
  rw [show expMeasure 1 = volume.withDensity (exponentialPDF 1) from rfl,
    gaussianReal_of_var_ne_zero 0 (by norm_num),
    prod_withDensity (by unfold exponentialPDF; fun_prop) (measurable_gaussianPDF 0 1)]
  rfl

/-- Full candidate-model pushforward to `C · (Exp(1) × N(0,1))`. -/
theorem map_source_eq_product {P : ℝ} (hP : 0 ≤ P) :
    Measure.map parabolic (volume.withDensity (sourceDensity P)) =
      ENNReal.ofReal (massConstant P) • modelMeasure := by
  rw [map_sourceDensity hP, ← withDensity_productDensity]
  exact withDensity_smul _ measurable_productDensity

/-- Exact right tail of the exponential density. -/
theorem exponential_right_tail {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ u in Set.Ioi R, exponentialPDF 1 u = ENNReal.ofReal (Real.exp (-R)) := by
  calc
    (∫⁻ u in Set.Ioi R, exponentialPDF 1 u) =
        ∫⁻ u in Set.Ioi R, ENNReal.ofReal (Real.exp (-u)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simp only [exponentialPDF_of_nonneg (hR.trans hu.le), one_mul]
    _ = ENNReal.ofReal (∫ u in Set.Ioi R, Real.exp (-u)) := by
      exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi R)
        (Filter.Eventually.of_forall fun u ↦ (Real.exp_pos (-u)).le)).symm
    _ = ENNReal.ofReal (Real.exp (-R)) := by rw [integral_exp_neg_Ioi]

/-- The model's radial marginal has the exact exponential tail. -/
theorem model_radial_tail {R : ℝ} (hR : 0 ≤ R) :
    modelMeasure (Set.Ioi R ×ˢ Set.univ) = ENNReal.ofReal (Real.exp (-R)) := by
  rw [modelMeasure, Measure.prod_prod, measure_univ, mul_one]
  change (volume.withDensity (exponentialPDF 1)) (Set.Ioi R) = _
  rw [withDensity_apply _ measurableSet_Ioi]
  exact exponential_right_tail hR

/-- The Gaussian marginal has vanishing two-sided tails. This statement is
about the model distribution, with no premise about zero measures. -/
theorem gaussian_two_sided_tail_tendsto :
    Filter.Tendsto (fun R : ℝ ↦ gaussianReal 0 1 {τ : ℝ | R < |τ|})
      Filter.atTop (𝓝 0) := by
  have hs : ∀ R : ℝ, NullMeasurableSet {τ : ℝ | R < |τ|} (gaussianReal 0 1) := by
    intro R
    exact (isOpen_lt continuous_const continuous_abs).measurableSet.nullMeasurableSet
  have hm : Antitone (fun R : ℝ ↦ {τ : ℝ | R < |τ|}) := by
    intro a b hab τ hτ
    exact hab.trans_lt hτ
  have hi : (⋂ R : ℝ, {τ : ℝ | R < |τ|}) = ∅ := by
    ext τ
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    exact (lt_irrefl |τ|) (h |τ|)
  have h := tendsto_measure_iInter_atTop hs hm
    ⟨0, measure_ne_top (gaussianReal 0 1) _⟩
  simpa only [Function.comp_def, hi, measure_empty] using h

/-- The same Gaussian tail statement for the product law's angular coordinate. -/
theorem model_angular_tail_tendsto :
    Filter.Tendsto (fun R : ℝ ↦ modelMeasure (Set.univ ×ˢ {τ : ℝ | R < |τ|}))
      Filter.atTop (𝓝 0) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  simpa only [modelMeasure, Measure.prod_prod, measure_univ, one_mul]
    using gaussian_two_sided_tail_tendsto

end
end V10.GaussianProfile
