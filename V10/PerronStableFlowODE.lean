import V10.PerronStableSubspace
import WasowVolterra
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Differentiating the actual uniformly-small mixed Volterra fixed point.
The backward weighted integrability follows from positive spectral real part
and bounded forcing; no L1 assumption on the perturbation is made. -/

namespace V10.PerronStableFlowODE
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
open V10.PerronStableSubspace

/-- The scalar backward integrating factor is integrable on the half-line
against any continuous bounded forcing. -/
theorem backward_weighted_integrable {lam : ℂ} {T M : ℝ} {h : ℝ → ℂ}
    (hlam : 0 < lam.re) (hc : Continuous h) (hb : ∀ s ≥ T, ‖h s‖ ≤ M) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(lam * s)) * h s) (Ici T) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp ((-lam.re) * s)) (Ici T) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi (neg_neg_of_pos hlam) T)
  apply (he.mul_const M).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  rw [norm_mul, Complex.norm_exp]
  have hexp : (-(lam * (s : ℂ))).re = (-lam.re) * s := by simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (hb s hs) (Real.exp_pos _).le

lemma phase_hasDerivAt (lam : ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => lam * t) lam r := by
  simpa using ((hasDerivAt_id r).ofReal_comp).const_mul lam

lemma homogeneous_hasDerivAt (lam ξ : ℂ) (T r : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (lam * ((t : ℂ) - T)) * ξ)
      (lam * (Complex.exp (lam * ((r : ℂ) - T)) * ξ)) r := by
  have h := ((((hasDerivAt_id r).ofReal_comp).sub_const (T : ℂ)).const_mul lam).cexp.mul_const ξ
  simpa only [id_eq, Complex.ofReal_one, mul_one, mul_assoc, mul_comm, mul_left_comm] using h

/-- A literal scalar mixed integral equation differentiates to its ODE. -/
theorem scalar_formula_hasDerivAt {u h : ℝ → ℂ} {T r M : ℝ} {lam ξ : ℂ}
    (mode : Bool) (hr : T < r) (hc : Continuous h)
    (hb : ∀ s ≥ T, ‖h s‖ ≤ M) (hgap : mode = false → 0 < lam.re)
    (hu : ∀ t ≥ T, u t = Complex.exp (lam * ((t : ℂ) - T)) * ξ +
      ∫ s in Ici T, MixedVolterra.kernel mode (fun v : ℝ => lam * v) t s * h s) :
    HasDerivAt u (lam * u r + h r) r := by
  have hback : mode = false →
      IntegrableOn (fun s : ℝ => Complex.exp (-(lam * s)) * h s) (Ici T) :=
    fun hm => backward_weighted_integrable (hgap hm) hc hb
  have hj := WasowVolterra.mixed_integral_hasDerivAt mode (fun t : ℝ => lam * t) h hr
    (phase_hasDerivAt lam r) (by fun_prop) hback
  have hd := (homogeneous_hasDerivAt lam ξ T r).add hj
  have heq : lam * (Complex.exp (lam * ((r : ℂ) - T)) * ξ) +
      (lam * (∫ s in Ici T, MixedVolterra.kernel mode (fun v : ℝ => lam * v) r s * h s) + h r) =
      lam * u r + h r := by rw [hu r hr.le]; ring
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact hu t ht.le

/-- The real cutoff kernel is exactly the restricted-half-line integral. -/
theorem kernel_integral_eq (T : ℝ) (mode : Bool) (lam : ℂ) (r : Ici T) (h : ℝ → ℂ) :
    (∫ s : ℝ, kernel T mode lam r s * h s) =
      ∫ s in Ici T, MixedVolterra.kernel mode (fun v : ℝ => lam * v) r s * h s := by
  have he : (fun s : ℝ => kernel T mode lam r s * h s) =
      (Ici T).indicator (fun s => MixedVolterra.kernel mode (fun v : ℝ => lam * v) r s * h s) := by
    funext s
    by_cases hs : T ≤ s <;> simp [kernel, hs]
  rw [he, integral_indicator measurableSet_Ici]

/-- Extend a half-line function by its endpoint value. This is only used to
express the ordinary ODE derivative in the interior of the half-line. -/
def extend {T : ℝ} {F : Type*} (u : Ici T → F) (t : ℝ) : F := u (clamp T t)

lemma extend_of_mem {T t : ℝ} {F : Type*} (u : Ici T → F) (ht : T ≤ t) :
    extend u t = u ⟨t, ht⟩ := by
  apply congrArg u
  apply Subtype.ext
  exact clamp_eq ht

variable {ι : Type*} [Fintype ι]

/-- A genuine bounded continuous fixed point of the actual mixed-kernel
formula satisfies the full diagonal-plus-perturbation ODE. -/
theorem fixed_point_hasDerivAt {T r M : ℝ} (mode : ι → Bool) (lam ξ : ι → ℂ)
    (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hRb : ∀ s, ‖R s‖ ≤ M) (u : Ici T →ᵇ (ι → ℂ))
    (hgap : ∀ i, mode i = false → 0 < (lam i).re)
    (hu : ∀ t i, u t i =
      (if mode i then Complex.exp (lam i * ((t : ℂ) - T)) * ξ i else 0) +
      ∫ s : ℝ, kernel T (mode i) (lam i) t s *
        (R (clamp T s) (u (clamp T s))) i)
    (hr : T < r) :
    HasDerivAt (extend u)
      (fun i => lam i * extend u r i + R (clamp T r) (extend u r) i) r := by
  apply hasDerivAt_pi.mpr
  intro i
  let h : ℝ → ℂ := fun s => (R (clamp T s) (u (clamp T s))) i
  have hc : Continuous h := by
    have hcl := continuous_clamp T
    have hucont := u.continuous
    dsimp [h]
    fun_prop
  have hb : ∀ s ≥ T, ‖h s‖ ≤ M * ‖u‖ := by
    intro s _
    exact (norm_le_pi_norm _ i).trans (((R (clamp T s)).le_opNorm _).trans
      (mul_le_mul (hRb _) (u.norm_coe_le_norm _) (norm_nonneg _)
        ((norm_nonneg (R (clamp T s))).trans (hRb (clamp T s)))))
  apply scalar_formula_hasDerivAt (ξ := if mode i then ξ i else 0)
    (mode i) hr hc hb (hgap i)
  intro t ht
  rw [extend_of_mem u ht]
  have hform := hu ⟨t, ht⟩ i
  rw [kernel_integral_eq] at hform
  cases hm : mode i <;> simpa only [hm, Bool.false_eq_true, ↓reduceIte,
    mul_zero, zero_add, h] using hform

#print axioms backward_weighted_integrable
#print axioms scalar_formula_hasDerivAt
#print axioms kernel_integral_eq
#print axioms fixed_point_hasDerivAt
end
end V10.PerronStableFlowODE
