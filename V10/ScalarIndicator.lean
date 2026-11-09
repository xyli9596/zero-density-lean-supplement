import V10.CompanionScalarWindow
import V10.PerronGeneral
import V10.PerronRadial
import V10.ScalarAnalytic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Scalar and vector ray indicators

The scalar ray logarithm is extended-real and is `-∞` at zeros. A uniformly
bounded forward observation window, proved from the actual companion ODE,
identifies its limsup with the vector logarithmic rate. Pointwise convergence
of the scalar logarithm is neither assumed nor asserted.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace V10.ScalarIndicator
open V10.CompanionObservation V10.CompanionShortFlow V10.CompanionScalarWindow
set_option backward.isDefEq.respectTransparency false

def scalarRayLog {n : ℕ} (Y : ℝ → State n) (r : ℝ) : EReal :=
  if Y r 0 = 0 then ⊥ else (Real.log ‖Y r 0‖ / r : ℝ)

/-- The extended-real scalar logarithm is bounded by the vector logarithm
for positive radii, including at actual scalar zeros. -/
theorem scalarRayLog_le_vector {n : ℕ} (Y : ℝ → State n) {r : ℝ} (hr : 0 < r) :
    scalarRayLog Y r ≤ (Real.log ‖Y r‖ / r : ℝ) := by
  by_cases hz : Y r 0 = 0
  · simp [scalarRayLog, hz]
  · simp only [scalarRayLog, if_neg hz]
    exact_mod_cast div_le_div_of_nonneg_right
      (Real.log_le_log (norm_pos_iff.mpr hz) (norm_le_pi_norm (Y r) 0)) hr.le

/-- The observation-window estimate identifies the actual scalar limsup.
The lower bound is used at moving scalar sample points, so zeros at other
radii cause no problem. -/
theorem limsup_scalar_eq_of_window {n : ℕ} {Y : ℝ → State n} {ℓ a : ℝ}
    (hlim : Tendsto (fun r => Real.log ‖Y r‖ / r) atTop (𝓝 ℓ))
    (hne : ∀ᶠ r : ℝ in atTop, Y r ≠ 0) (ha : 0 < a)
    (hwindow : ∀ᶠ r : ℝ in atTop, ∃ t ∈ Icc (0 : ℝ) 1,
      a * ‖Y r‖ ≤ ‖Y (r + t) 0‖) :
    limsup (scalarRayLog Y) atTop = (ℓ : EReal) := by
  classical
  have hupper : limsup (scalarRayLog Y) atTop ≤ (ℓ : EReal) := by
    have hcmp : ∀ᶠ r : ℝ in atTop, scalarRayLog Y r ≤ (Real.log ‖Y r‖ / r : ℝ) :=
      (eventually_gt_atTop (0 : ℝ)).mono fun r hr => scalarRayLog_le_vector Y hr
    have hE : Tendsto (fun r => ((Real.log ‖Y r‖ / r : ℝ) : EReal)) atTop (𝓝 (ℓ : EReal)) :=
      EReal.tendsto_coe.mpr hlim
    exact (limsup_le_limsup hcmp).trans_eq hE.limsup_eq
  obtain ⟨R, hR⟩ := eventually_atTop.mp hwindow
  have hex (r : ℝ) : ∃ t ∈ Icc (0 : ℝ) 1,
      R ≤ r → a * ‖Y r‖ ≤ ‖Y (r + t) 0‖ := by
    by_cases hr : R ≤ r
    · obtain ⟨t, ht, hb⟩ := hR r hr
      exact ⟨t, ht, fun _ => hb⟩
    · exact ⟨0, by constructor <;> norm_num, fun h => (hr h).elim⟩
  choose τ hτ hτobs using hex
  let s : ℝ → ℝ := fun r => r + τ r
  have hsge : ∀ r, r ≤ s r := fun r => by dsimp [s]; linarith [(hτ r).1]
  have hs : Tendsto s atTop atTop := tendsto_atTop_mono hsge tendsto_id
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r ∧ 0 < s r :=
    (eventually_gt_atTop (0 : ℝ)).mono fun r hr => ⟨hr, hr.trans_le (hsge r)⟩
  have hsnonzero : ∀ᶠ r : ℝ in atTop, Y (s r) 0 ≠ 0 := by
    filter_upwards [hne, eventually_ge_atTop R] with r hr hRr
    have hp := (mul_pos ha (norm_pos_iff.mpr hr)).trans_le (hτobs r hRr)
    exact norm_pos_iff.mp hp
  have hτdiv : Tendsto (fun r => τ r / s r) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall fun r => (hτ r).1) (Eventually.of_forall fun r => (hτ r).2) hs
  have hratio : Tendsto (fun r => r / s r) atTop (𝓝 1) := by
    have hh : Tendsto (fun r => (1 : ℝ) - τ r / s r) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hτdiv
    have he : (fun r => (1 : ℝ) - τ r / s r) =ᶠ[atTop] (fun r => r / s r) := by
      filter_upwards [hpos] with r hr
      have heq : r = s r - τ r := by dsimp [s]; ring
      calc
        1 - τ r / s r = (s r - τ r) / s r := by rw [sub_div, div_self hr.2.ne']
        _ = r / s r := by rw [← heq]
    exact hh.congr' he
  have hlogdiv : Tendsto (fun r : ℝ => Real.log a / r) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (Eventually.of_forall fun _ => le_rfl)
      (Eventually.of_forall fun _ => le_rfl) tendsto_id
  have hlower : Tendsto (fun r => (Real.log a + Real.log ‖Y r‖) / s r) atTop (𝓝 ℓ) := by
    have hh := (hlim.add hlogdiv).mul hratio
    have he : (fun r => (Real.log ‖Y r‖ / r + Real.log a / r) * (r / s r)) =ᶠ[atTop]
        (fun r => (Real.log a + Real.log ‖Y r‖) / s r) := by
      filter_upwards [hpos] with r hr
      field_simp [hr.1.ne', hr.2.ne']
      ring
    have hh' : Tendsto (fun r => (Real.log ‖Y r‖ / r + Real.log a / r) * (r / s r))
        atTop (𝓝 ℓ) := by simpa only [add_zero, mul_one] using hh
    exact hh'.congr' he
  have hsample : Tendsto (fun r => Real.log ‖Y (s r) 0‖ / s r) atTop (𝓝 ℓ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower (hlim.comp hs)
    · filter_upwards [hne, hsnonzero, hpos, eventually_ge_atTop R] with r hr hsr hp hRr
      have he := Real.log_le_log (mul_pos ha (norm_pos_iff.mpr hr)) (hτobs r hRr)
      rw [Real.log_mul ha.ne' (norm_ne_zero_iff.mpr hr)] at he
      exact div_le_div_of_nonneg_right he hp.2.le
    · filter_upwards [hsnonzero, hpos] with r hr hp
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (norm_pos_iff.mpr hr) (norm_le_pi_norm (Y (s r)) 0)) hp.2.le
  have hsampleE : Tendsto (scalarRayLog Y ∘ s) atTop (𝓝 (ℓ : EReal)) := by
    apply (EReal.tendsto_coe.mpr hsample).congr'
    filter_upwards [hsnonzero] with r hr
    simp [scalarRayLog, hr]
  exact le_antisymm hupper (hsampleE.limsup_eq.symm.trans_le hs.limsup_comp_le_limsup)

/-- Actual companion coefficient convergence and the actual solution ODE
identify scalar and vector rates. Perron's theorem can supply the vector limit. -/
theorem actual_scalar_indicator_eq {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {A : ℝ → Operator n} {Y : ℝ → State n} {ℓ : ℝ}
    (hA : Tendsto A atTop (𝓝 (ζ • companion b)))
    (hode : ∀ᶠ r : ℝ in atTop, HasDerivAt Y (A r (Y r)) r)
    (hne : ∀ᶠ r : ℝ in atTop, Y r ≠ 0)
    (hlim : Tendsto (fun r => Real.log ‖Y r‖ / r) atTop (𝓝 ℓ)) :
    limsup (scalarRayLog Y) atTop = (ℓ : EReal) := by
  obtain ⟨a, ha, hwindow⟩ := actual_companion_scalar_window b hζ hA hode
  exact limsup_scalar_eq_of_window hlim hne ha hwindow

/-- Perron's theorem supplies the rate and nonvanishing inside this endpoint;
the conclusion classifies the actual scalar indicator by actual eigenvalues. -/
theorem perron_scalar_classification {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {A : ℝ → Operator n} {Y : ℝ → State n} {T : ℝ}
    (hcont : ContinuousOn A (Ici T))
    (hA : Tendsto A atTop (𝓝 (ζ • companion b)))
    (hode : ∀ r ≥ T, HasDerivAt Y (A r (Y r)) r) (hY : Y T ≠ 0) :
    ∃ μ : Module.End.Eigenvalues (ζ • (companion b).toLinearMap),
      Tendsto (fun r => Real.log ‖Y r‖ / r) atTop (𝓝 μ.val.re) ∧
      limsup (scalarRayLog Y) atTop = (μ.val.re : EReal) := by
  obtain ⟨μ, hμ⟩ := V10.PerronGeneral.perron_growth_exponent hcont hA hode hY
  refine ⟨μ, hμ, actual_scalar_indicator_eq b hζ hA ?_ ?_ hμ⟩
  · exact (eventually_ge_atTop T).mono fun r hr => hode r hr
  · exact (eventually_ge_atTop T).mono fun r hr =>
      (V10.PerronGeneral.complex_solution_bounds hcont hA hode hY).1 r hr

/-- The scalar indicator on an actual complex ray, taking `-∞` at zeros. -/
def rayIndicator (v : ℂ → ℂ) (ζ : ℂ) : EReal :=
  limsup (fun r : ℝ => if v ((r : ℂ) * ζ) = 0 then ⊥ else
    ((Real.log ‖v ((r : ℂ) * ζ)‖ / r : ℝ) : EReal)) atTop

/-- The scalar spectral classification and equality to the actual vector rate
on a complex ray, directly from the actual derivative-jet ODE. -/
theorem actual_jet_ray_classification {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {A : ℂ → Operator n} {v : ℂ → ℂ} {S : Set ℂ} {T : ℝ}
    (hcont : ContinuousOn A S) (hray : ∀ r ≥ T, (r : ℂ) * ζ ∈ S)
    (hA : Tendsto (fun r : ℝ => A ((r : ℂ) * ζ)) atTop (𝓝 (companion b)))
    (hode : ∀ z ∈ S, HasDerivAt (ZeroDensity.ScalarLimit.jet (n + 1) v)
      (A z (ZeroDensity.ScalarLimit.jet (n + 1) v z)) z)
    (hY : ZeroDensity.ScalarLimit.jet (n + 1) v ((T : ℂ) * ζ) ≠ 0) :
    ∃ μ : Module.End.Eigenvalues (companion b).toLinearMap,
      Tendsto (fun r : ℝ => Real.log
        ‖ZeroDensity.ScalarLimit.jet (n + 1) v ((r : ℂ) * ζ)‖ / r)
        atTop (𝓝 (μ.val * ζ).re) ∧
      rayIndicator v ζ = ((μ.val * ζ).re : EReal) := by
  obtain ⟨μ, hμ⟩ := V10.PerronRadial.ray_growth_exponent hζ hcont hray hA hode hY
  have hc := V10.PerronRadial.ray_coefficient_continuousOn hcont hray
  have hl := V10.PerronRadial.ray_coefficient_tendsto ζ hA
  have ho := fun r hr => V10.PerronRadial.ray_hasDerivAt (hode _ (hray r hr))
  have he := actual_scalar_indicator_eq b hζ hl
    ((eventually_ge_atTop T).mono fun r hr => ho r hr)
    ((eventually_ge_atTop T).mono fun r hr =>
      (V10.PerronGeneral.complex_solution_bounds hc hl ho hY).1 r hr) hμ
  refine ⟨μ, hμ, ?_⟩
  rw [rayIndicator]
  convert he using 1
  congr 1

#print axioms limsup_scalar_eq_of_window
#print axioms actual_scalar_indicator_eq
#print axioms actual_jet_ray_classification

end V10.ScalarIndicator
