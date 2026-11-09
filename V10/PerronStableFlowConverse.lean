import V10.PerronStableFlowODE
import V10.PerronStableSubspaceForcing
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Bounded actual ODE solutions satisfy the mixed Volterra formula.
The backward boundary value at infinity is proved, not supplied as data. -/
namespace V10.PerronStableFlowODE
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
open V10.PerronStableSubspace

lemma integrating_factor_hasDerivAt {u h : ℝ → ℂ} {lam : ℂ} {r : ℝ}
    (hu : HasDerivAt u (lam * u r + h r) r) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(lam * t)) * u t)
      (Complex.exp (-(lam * r)) * h r) r := by
  have hh := ((phase_hasDerivAt lam r).neg.cexp).mul hu
  change HasDerivAt (fun t : ℝ => Complex.exp (-(lam * t)) * u t)
    (Complex.exp (-(lam * r)) * (-lam) * u r +
      Complex.exp (-(lam * r)) * (lam * u r + h r)) r at hh
  convert hh using 1
  ring

/-- Finite-interval variation of constants, requiring no derivative at the
initial endpoint. -/
theorem forward_formula_of_ode {u h : ℝ → ℂ} {T r : ℝ} {lam : ℂ}
    (hu : Continuous u) (hh : Continuous h)
    (hode : ∀ t > T, HasDerivAt u (lam * u t + h t) t) (hr : T ≤ r) :
    u r = Complex.exp (lam * ((r : ℂ) - T)) * u T +
      ∫ s in Ici T, MixedVolterra.kernel true (fun v : ℝ => lam * v) r s * h s := by
  rw [WasowVolterra.forward_integral_eq _ _ hr]
  have hint : (∫ s in T..r, Complex.exp (-(lam * s)) * h s) =
      Complex.exp (-(lam * r)) * u r - Complex.exp (-(lam * T)) * u T := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr (by fun_prop)
    · intro t ht
      exact integrating_factor_hasDerivAt (hode t ht.1)
    · exact (by fun_prop : Continuous (fun s : ℝ => Complex.exp (-(lam * s)) * h s)).intervalIntegrable _ _
  rw [hint]
  have he : Complex.exp (lam * ((r : ℂ) - T)) =
      Complex.exp (lam * r) * Complex.exp (-(lam * T)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  have hc : Complex.exp (lam * r) * Complex.exp (-(lam * r)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc
    u r = (Complex.exp (lam * r) * Complex.exp (-(lam * r))) * u r := by rw [hc, one_mul]
    _ = _ := by ring

/-- For a bounded solution, the unstable integrating factor has zero boundary
value at infinity; the backward integral formula therefore follows from FTC. -/
theorem backward_formula_of_ode {u h : ℝ → ℂ} {T r M N : ℝ} {lam : ℂ}
    (hlam : 0 < lam.re) (hu : Continuous u) (hh : Continuous h)
    (hub : ∀ t ≥ T, ‖u t‖ ≤ M) (hhb : ∀ t ≥ T, ‖h t‖ ≤ N)
    (hode : ∀ t > T, HasDerivAt u (lam * u t + h t) t) (hr : T ≤ r) :
    u r = ∫ s in Ici T, MixedVolterra.kernel false (fun v : ℝ => lam * v) r s * h s := by
  have huid := backward_weighted_integrable hlam hu hub
  have hhid := backward_weighted_integrable hlam hh hhb
  have hd : ∀ t ∈ Ioi T, HasDerivAt (fun s : ℝ => Complex.exp (-(lam * s)) * u s)
      (Complex.exp (-(lam * t)) * h t) t := fun t ht =>
    integrating_factor_hasDerivAt (hode t ht)
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (hhid.mono_set Ioi_subset_Ici_self) (huid.mono_set Ioi_subset_Ici_self)
  have hint : (∫ s in Ioi r, Complex.exp (-(lam * s)) * h s) =
      - (Complex.exp (-(lam * r)) * u r) := by
    simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto
      (by fun_prop : ContinuousWithinAt (fun s : ℝ => Complex.exp (-(lam * s)) * u s) (Ici r) r)
      (fun t ht => integrating_factor_hasDerivAt (hode t (lt_of_le_of_lt hr ht)))
      (hhid.mono_set (fun t ht => le_trans hr ht.le)) hzero
  rw [WasowVolterra.backward_integral_eq _ _ hr, integral_Ici_eq_integral_Ioi, hint]
  simp only [neg_mul_neg, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]

variable {ι : Type*} [Fintype ι]

/-- The exact pointwise mixed formula for every bounded continuous solution.
Only interior ODE derivatives are required. -/
theorem bounded_ode_formula {T M : ℝ} (mode : ι → Bool) (lam : ι → ℂ)
    (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
    (hRb : ∀ s, ‖R s‖ ≤ M) (u : Ici T →ᵇ (ι → ℂ))
    (hgap : ∀ i, mode i = false → 0 < (lam i).re)
    (hode : ∀ r > T, HasDerivAt (extend u)
      (fun i => lam i * extend u r i + R (clamp T r) (extend u r) i) r) :
    ∀ t i, u t i =
      (if mode i then Complex.exp (lam i * ((t : ℂ) - T)) * u ⟨T, by exact le_refl T⟩ i else 0) +
      ∫ s : ℝ, kernel T (mode i) (lam i) t s *
        (R (clamp T s) (u (clamp T s))) i := by
  intro t i
  let ui : ℝ → ℂ := fun r => extend u r i
  let hi : ℝ → ℂ := fun r => (R (clamp T r) (u (clamp T r))) i
  have hcl := continuous_clamp T
  have huc := u.continuous
  have hui : Continuous ui := by dsimp [ui, extend]; fun_prop
  have hhi : Continuous hi := by dsimp [hi]; fun_prop
  have huiB : ∀ r ≥ T, ‖ui r‖ ≤ ‖u‖ := fun r _ =>
    (norm_le_pi_norm _ i).trans (u.norm_coe_le_norm _)
  have hhiB : ∀ r ≥ T, ‖hi r‖ ≤ M * ‖u‖ := by
    intro r _
    exact (norm_le_pi_norm _ i).trans (((R (clamp T r)).le_opNorm _).trans
      (mul_le_mul (hRb _) (u.norm_coe_le_norm _) (norm_nonneg _)
        ((norm_nonneg (R (clamp T r))).trans (hRb (clamp T r)))))
  have hdi : ∀ r > T, HasDerivAt ui (lam i * ui r + hi r) r := by
    intro r hr
    exact (hasDerivAt_pi.mp (hode r hr)) i
  rw [kernel_integral_eq]
  cases hm : mode i
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    have hf := backward_formula_of_ode (hgap i hm) hui hhi huiB hhiB hdi t.property
    simpa only [ui, hi, extend_of_mem u t.property] using hf
  · simp only [↓reduceIte]
    have hf := forward_formula_of_ode hui hhi hdi t.property
    simpa only [ui, hi, extend_of_mem u t.property, extend_of_mem u (le_refl T)] using hf

#print axioms forward_formula_of_ode
#print axioms backward_formula_of_ode
#print axioms bounded_ode_formula
end
end V10.PerronStableFlowODE
