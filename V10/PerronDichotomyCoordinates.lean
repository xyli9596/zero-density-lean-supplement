import V10.PerronDichotomy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual coordinate energies for Perron's dichotomy

Finite coordinate energies are differentiated from the actual complex ODE.
Perturbation estimates use its actual continuous-linear-map operator norm.
The remaining spectral input is the dissipative quadratic-form bound for
stable/unstable blocks in an adapted basis, supplied by spectral reduction.
-/

namespace V10.PerronDichotomyCoordinates
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Euclidean squared energy of the selected finite coordinates. -/
def energy (s : Finset ι) (x : ι → ℂ) : ℝ := ∑ i ∈ s, ‖x i‖ ^ 2

/-- The real quadratic pairing that differentiates coordinate energy. -/
def pairing (s : Finset ι) (x y : ι → ℂ) : ℝ := ∑ i ∈ s, inner ℝ (x i) (y i)

omit [Fintype ι] [DecidableEq ι] in
lemma energy_nonneg (s : Finset ι) (x : ι → ℂ) : 0 ≤ energy s x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma energy_add_compl (s : Finset ι) (x : ι → ℂ) :
    energy s x + energy sᶜ x = energy Finset.univ x := by
  exact Finset.sum_add_sum_compl s _

omit [DecidableEq ι] in
lemma norm_sq_le_energy (x : ι → ℂ) : ‖x‖ ^ 2 ≤ energy Finset.univ x := by
  have he := energy_nonneg Finset.univ x
  have hnorm : ‖x‖ ≤ Real.sqrt (energy Finset.univ x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) he).mpr
    exact Finset.single_le_sum (f := fun j : ι => ‖x j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnorm
  rwa [Real.sq_sqrt he] at hh

omit [DecidableEq ι] in
lemma energy_pos_of_ne_zero {x : ι → ℂ} (hx : x ≠ 0) :
    0 < energy Finset.univ x :=
  (sq_pos_of_pos (norm_pos_iff.mpr hx)).trans_le (norm_sq_le_energy x)

omit [DecidableEq ι] in
lemma energy_le_card_norm_sq (s : Finset ι) (x : ι → ℂ) :
    energy s x ≤ (s.card : ℝ) * ‖x‖ ^ 2 := by
  apply (Finset.sum_le_sum (fun i (_ : i ∈ s) =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm x i))).trans
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma pairing_add_right (s : Finset ι) (x y z : ι → ℂ) :
    pairing s x (y + z) = pairing s x y + pairing s x z := by
  simp [pairing, inner_add_right, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] in
lemma pairing_eq_re_sum (s : Finset ι) (x y : ι → ℂ) :
    pairing s x y = ∑ i ∈ s, (star (x i) * y i).re := by
  apply Finset.sum_congr rfl
  intro i _
  simp [real_inner_eq_re_inner ℂ, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Differentiate the actual sum of squared coordinate norms. -/
theorem energy_hasDerivAt {x : ℝ → ι → ℂ} {x' : ι → ℂ} {t : ℝ} (s : Finset ι)
    (hx : ∀ i ∈ s, HasDerivAt (fun u => x u i) (x' i) t) :
    HasDerivAt (fun u => energy s (x u)) (2 * pairing s (x t) x') t := by
  simpa only [energy, pairing, Finset.mul_sum] using
    (HasDerivAt.fun_sum (fun i hi => (hx i hi).norm_sq))

omit [DecidableEq ι] in
/-- A concrete perturbation pairing bound from the actual operator norm.
It works with the ordinary sup norm on finite coordinate functions. -/
theorem abs_pairing_operator_le (s : Finset ι) (B : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (x : ι → ℂ) :
    |pairing s x (B x)| ≤ (s.card : ℝ) * ‖B‖ * energy Finset.univ x := by
  have hterm : ∀ i ∈ s, |inner ℝ (x i) (B x i)| ≤ ‖B‖ * ‖x‖ ^ 2 := by
    intro i _
    calc
      |inner ℝ (x i) (B x i)| ≤ ‖x i‖ * ‖B x i‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖B x‖ := mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm (B x) i)
        (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
      _ = ‖B‖ * ‖x‖ ^ 2 := by ring
  calc
    |pairing s x (B x)| ≤ ∑ i ∈ s, |inner ℝ (x i) (B x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, ‖B‖ * ‖x‖ ^ 2 := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * ‖B‖ * ‖x‖ ^ 2 := by simp [mul_assoc]
    _ ≤ (s.card : ℝ) * ‖B‖ * energy Finset.univ x :=
      mul_le_mul_of_nonneg_left (norm_sq_le_energy x) (by positivity)

omit [DecidableEq ι] in
/-- Small actual operator norm controls twice the perturbation pairing on
every coordinate block by δ times the full Euclidean energy. -/
theorem twice_abs_pairing_le {B : (ι → ℂ) →L[ℂ] (ι → ℂ)} {δ : ℝ}
    (hB : 2 * (Fintype.card ι : ℝ) * ‖B‖ ≤ δ) (s : Finset ι) (x : ι → ℂ) :
    2 * |pairing s x (B x)| ≤ δ * energy Finset.univ x := by
  have hcard : (s.card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Finset.card_le_univ s
  have hcoef : 2 * (s.card : ℝ) * ‖B‖ ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_right hcard (norm_nonneg B)
    linarith
  calc
    2 * |pairing s x (B x)| ≤ 2 * ((s.card : ℝ) * ‖B‖ * energy Finset.univ x) :=
      mul_le_mul_of_nonneg_left (abs_pairing_operator_le s B x) (by norm_num)
    _ = (2 * (s.card : ℝ) * ‖B‖) * energy Finset.univ x := by ring
    _ ≤ δ * energy Finset.univ x :=
      mul_le_mul_of_nonneg_right hcoef (energy_nonneg _ _)

/-- A genuine two-block dichotomy for an actual complex-linear ODE in finite
coordinates. Spectral quadratic-form bounds are inputs, but neither energy
derivatives nor either growth alternative is assumed. -/
theorem actual_coordinate_ode_dichotomy
    {A : (ι → ℂ) →L[ℂ] (ι → ℂ)} {B : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {x : ℝ → ι → ℂ} (s : Finset ι) {T γ δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ t ≥ T, HasDerivAt x (A (x t) + B t (x t)) t)
    (hx : ∀ t ≥ T, x t ≠ 0)
    (hstable : ∀ y, pairing s y (A y) ≤ (γ - 2 * δ) * energy s y)
    (hunstable : ∀ y, (γ + 2 * δ) * energy sᶜ y ≤ pairing sᶜ y (A y))
    (hB : ∀ t ≥ T, 2 * (Fintype.card ι : ℝ) * ‖B t‖ ≤ δ) :
    (∃ C : ℝ, 0 < C ∧ ∀ t ≥ T,
      energy Finset.univ (x t) ≤ C * Real.exp (2 * (γ - δ) * (t - T))) ∨
    (∃ T₁ ≥ T, ∃ C : ℝ, 0 < C ∧ ∀ t ≥ T₁,
      C * Real.exp (2 * (γ + δ) * (t - T₁)) ≤ energy Finset.univ (x t)) := by
  have hsder : ∀ t ≥ T, HasDerivAt (fun u => energy s (x u))
      (2 * pairing s (x t) (A (x t) + B t (x t))) t := by
    intro t ht
    exact energy_hasDerivAt s (fun i _ => hasDerivAt_pi.mp (hode t ht) i)
  have huder : ∀ t ≥ T, HasDerivAt (fun u => energy sᶜ (x u))
      (2 * pairing sᶜ (x t) (A (x t) + B t (x t))) t := by
    intro t ht
    exact energy_hasDerivAt sᶜ (fun i _ => hasDerivAt_pi.mp (hode t ht) i)
  have hst : ∀ t ≥ T,
      2 * pairing s (x t) (A (x t) + B t (x t)) ≤
        2 * (γ - 2 * δ) * energy s (x t) +
          δ * (energy s (x t) + energy sᶜ (x t)) := by
    intro t ht
    rw [pairing_add_right, energy_add_compl]
    have h := hstable (x t)
    have hb := twice_abs_pairing_le (hB t ht) s (x t)
    have hp := le_abs_self (pairing s (x t) (B t (x t)))
    nlinarith
  have hut : ∀ t ≥ T,
      2 * (γ + 2 * δ) * energy sᶜ (x t) -
          δ * (energy s (x t) + energy sᶜ (x t)) ≤
        2 * pairing sᶜ (x t) (A (x t) + B t (x t)) := by
    intro t ht
    rw [pairing_add_right, energy_add_compl]
    have h := hunstable (x t)
    have hb := twice_abs_pairing_le (hB t ht) sᶜ (x t)
    have hp := neg_abs_le (pairing sᶜ (x t) (B t (x t)))
    nlinarith
  have hc := V10.PerronDichotomy.energy_dichotomy hδ hsder huder
    (fun t _ => ⟨energy_nonneg s (x t), energy_nonneg sᶜ (x t)⟩)
    (fun t ht => by rw [energy_add_compl]; exact energy_pos_of_ne_zero (hx t ht)) hst hut
  simpa only [energy_add_compl] using hc

omit [DecidableEq ι] in
/-- Convergence of the actual perturbation operator gives the quantitative
smallness needed by the cone argument; no error envelope is assumed. -/
theorem eventually_small_operator {B : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hB : Tendsto B atTop (𝓝 0)) :
    ∀ᶠ t in atTop, 2 * (Fintype.card ι : ℝ) * ‖B t‖ ≤ δ := by
  have hnorm : Tendsto (fun t => ‖B t‖) atTop (𝓝 0) := by simpa using hB.norm
  have hlim : Tendsto (fun t => 2 * (Fintype.card ι : ℝ) * ‖B t‖) atTop (𝓝 0) := by
    simpa using hnorm.const_mul (2 * (Fintype.card ι : ℝ))
  exact (hlim.eventually (eventually_lt_nhds hδ)).mono fun _ h => h.le

omit [DecidableEq ι] in
/-- Nonvanishing follows from the actual ODE and locally bounded continuous
coefficients. It is not an additional all-time hypothesis on the trajectory. -/
theorem coordinate_solution_ne_zero
    {A : (ι → ℂ) →L[ℂ] (ι → ℂ)} {B : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {x : ℝ → ι → ℂ} {T t : ℝ} (ht : T ≤ t)
    (hode : ∀ u ≥ T, HasDerivAt x (A (x u) + B u (x u)) u)
    (hB : ContinuousOn B (Ici T)) (hx : x T ≠ 0) : x t ≠ 0 := by
  have hcont : ContinuousOn B (Icc T t) := hB.mono (fun _ hu => hu.1)
  obtain ⟨K, hK, hbound⟩ := ((isCompact_Icc.image_of_continuousOn hcont).isBounded).exists_pos_norm_le
  apply ZeroDensity.PerronEstimates.solution_ne_zero
    (A := fun u => (A + B u).restrictScalars ℝ) (K := ‖A‖ + K) ht
    (fun u hu => ?_) (fun u hu => ?_) hx
  · change HasDerivAt x (A (x u) + B u (x u)) u
    exact hode u hu.1
  · rw [ContinuousLinearMap.norm_restrictScalars]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hbound _ (mem_image_of_mem B hu)))

/-- The actual asymptotically constant ODE has a two-block exponential
alternative once the constant operator has the stated spectral energy gap.
The small perturbation time and nonvanishing are both proved here. -/
theorem actual_asymptotic_coordinate_dichotomy
    {A : (ι → ℂ) →L[ℂ] (ι → ℂ)} {B : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)}
    {x : ℝ → ι → ℂ} (s : Finset ι) {T₀ γ δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ t ≥ T₀, HasDerivAt x (A (x t) + B t (x t)) t)
    (hx : x T₀ ≠ 0) (hBcont : ContinuousOn B (Ici T₀))
    (hstable : ∀ y, pairing s y (A y) ≤ (γ - 2 * δ) * energy s y)
    (hunstable : ∀ y, (γ + 2 * δ) * energy sᶜ y ≤ pairing sᶜ y (A y))
    (hBlim : Tendsto B atTop (𝓝 0)) :
    ∃ T ≥ T₀,
      (∃ C : ℝ, 0 < C ∧ ∀ t ≥ T,
        energy Finset.univ (x t) ≤ C * Real.exp (2 * (γ - δ) * (t - T))) ∨
      (∃ T₁ ≥ T, ∃ C : ℝ, 0 < C ∧ ∀ t ≥ T₁,
        C * Real.exp (2 * (γ + δ) * (t - T₁)) ≤ energy Finset.univ (x t)) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_small_operator hδ hBlim)
  refine ⟨max T₀ R, le_max_left _ _, ?_⟩
  exact actual_coordinate_ode_dichotomy s hδ
    (fun t ht => hode t ((le_max_left _ _).trans ht))
    (fun t ht => coordinate_solution_ne_zero ((le_max_left _ _).trans ht) hode hBcont hx)
    hstable hunstable (fun t ht => hR t ((le_max_right _ _).trans ht))

#print axioms norm_sq_le_energy
#print axioms energy_hasDerivAt
#print axioms abs_pairing_operator_le
#print axioms actual_coordinate_ode_dichotomy
#print axioms eventually_small_operator
#print axioms coordinate_solution_ne_zero
#print axioms actual_asymptotic_coordinate_dichotomy
end
end V10.PerronDichotomyCoordinates
