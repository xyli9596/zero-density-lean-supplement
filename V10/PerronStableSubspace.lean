import MixedVolterra
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral

/-! Exponentially decaying mixed Volterra kernels on an actual half-line.
Unlike the inherited L1-tail operator, these bounds allow a uniformly small
continuous perturbation which need not be integrable. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace V10.PerronStableSubspace

def decay (δ r s : ℝ) : ℝ := Real.exp (-δ * |r - s|)
def decayMass (δ : ℝ) : ℝ := ∫ s : ℝ, Real.exp (-δ * |s|)

lemma decay_nonneg (δ r s : ℝ) : 0 ≤ decay δ r s := (Real.exp_pos _).le

lemma integrable_exp_neg_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun s : ℝ => Real.exp (-δ * |s|)) := by
  rw [← integrableOn_univ, ← @Iic_union_Ioi ℝ _ (0 : ℝ), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hδ 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    congr 1
    rw [abs_of_nonpos hs]
    ring
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hδ) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [abs_of_pos hs]

lemma integrable_decay {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : Integrable (decay δ r) :=
  (integrable_exp_neg_abs hδ).comp_sub_left r

lemma integral_decay (δ r : ℝ) : (∫ s : ℝ, decay δ r s) = decayMass δ := by
  exact integral_sub_left_eq_self (fun s : ℝ => Real.exp (-δ * |s|)) volume r

lemma decayMass_nonneg (δ : ℝ) : 0 ≤ decayMass δ :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- A local uniform integrable majorant in the parameter variable. -/
lemma decay_local_bound {δ r t s : ℝ} (hδ : 0 ≤ δ) (htr : |t - r| ≤ 1) :
    decay δ t s ≤ Real.exp δ * decay δ r s := by
  rw [decay, decay, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : |r - s| ≤ |t - r| + |t - s| := by
    calc
      _ ≤ |r - t| + |t - s| := abs_sub_le r t s
      _ = _ := by rw [abs_sub_comm r t]
  nlinarith

/-- Clamp the integration variable to the half-line when evaluating its functions. -/
def clamp (T s : ℝ) : Ici T := ⟨max T s, by exact le_max_left T s⟩

lemma continuous_clamp (T : ℝ) : Continuous (clamp T) := by
  unfold clamp
  fun_prop

lemma clamp_eq {T s : ℝ} (hs : T ≤ s) : (clamp T s : ℝ) = s := by
  change max T s = s
  exact max_eq_right hs

/-- The actual forward/backward scalar kernel, with a lower-endpoint cutoff. -/
def kernel (T : ℝ) (forward : Bool) (lam : ℂ) (r : Ici T) (s : ℝ) : ℂ :=
  if T ≤ s then MixedVolterra.kernel forward (fun t : ℝ => lam * t) r s else 0

lemma kernel_bound {T δ : ℝ} (forward : Bool) (lam : ℂ)
    (hgap : if forward then lam.re ≤ -δ else δ ≤ lam.re) (r : Ici T) (s : ℝ) :
    ‖kernel T forward lam r s‖ ≤ decay δ r s := by
  by_cases hT : T ≤ s
  · simp only [kernel, hT, if_true]
    cases forward
    · simp only [Bool.false_eq_true, ↓reduceIte, MixedVolterra.kernel] at hgap ⊢
      split_ifs with hrs
      · rw [norm_neg, Complex.norm_exp, decay]
        apply Real.exp_le_exp.mpr
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        rw [abs_of_nonpos (sub_nonpos.mpr hrs)]
        nlinarith
      · simpa using decay_nonneg δ r s
    · simp only [↓reduceIte, MixedVolterra.kernel] at hgap ⊢
      split_ifs with hsr
      · rw [Complex.norm_exp, decay]
        apply Real.exp_le_exp.mpr
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        rw [abs_of_nonneg (sub_nonneg.mpr hsr)]
        nlinarith
      · simpa using decay_nonneg δ r s
  · simpa [kernel, hT] using decay_nonneg δ r s

lemma kernel_measurable (T : ℝ) (forward : Bool) (lam : ℂ) (r : Ici T) :
    Measurable (kernel T forward lam r) :=
  (MixedVolterra.kernel_measurable forward (fun t : ℝ => lam * t)
    (by fun_prop) r).ite measurableSet_Ici measurable_const

lemma kernel_continuousAt (T : ℝ) (forward : Bool) (lam : ℂ) (r : Ici T) (s : ℝ)
    (hs : s ≠ (r : ℝ)) : ContinuousAt (fun t : Ici T => kernel T forward lam t s) r := by
  by_cases hT : T ≤ s
  · simp only [kernel, hT, if_true]
    exact (MixedVolterra.kernel_continuousAt forward (fun t : ℝ => lam * t)
      (by fun_prop) r s hs).comp continuous_subtype_val.continuousAt
  · simp only [kernel, hT, if_false]
    exact continuousAt_const

end V10.PerronStableSubspace
