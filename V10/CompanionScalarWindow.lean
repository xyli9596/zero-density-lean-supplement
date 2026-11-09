import V10.CompanionShortFlow

/-!
# Scalar observation of actual asymptotically companion solutions

The comparison is applied directly to the actual solution, so no fundamental
matrix or representation formula is supplied as an extra hypothesis.
-/

noncomputable section
open Set Filter NormedSpace
open scoped Topology
namespace V10.CompanionScalarWindow
open V10.CompanionObservation V10.CompanionShortFlow
set_option backward.isDefEq.respectTransparency false

theorem gronwall_zero_mul (M ε c t : ℝ) :
    gronwallBound 0 M (ε * c) t = gronwallBound 0 M ε t * c := by
  unfold gronwallBound
  split_ifs <;> ring

/-- Relative trajectory error on one observation interval. The error is
proportional to the actual initial norm, including when that norm is zero. -/
theorem trajectory_error_bound {n : ℕ} {B : Operator n} {C : ℝ → Operator n}
    {Y : ℝ → State n} {M K ε : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Y (C t (Y t)) t)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t‖ ≤ M)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t - B‖ ≤ ε)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ‖flow B t‖ ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖Y t - trajectory B (Y 0) t‖ ≤
      gronwallBound 0 M (ε * K) 1 * ‖Y 0‖ := by
  have hcY : ContinuousOn Y (Icc (0 : ℝ) 1) :=
    fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hc := hcY.sub (trajectory_continuous B (Y 0)).continuousOn
  have hd : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Y t - trajectory B (Y 0) t)
        (C t (Y t) - B (trajectory B (Y 0) t)) (Ici t) t :=
    fun t ht => ((hY t (Ico_subset_Icc_self ht)).sub
      (trajectory_hasDerivAt B (Y 0) t)).hasDerivWithinAt
  have hinit : ‖Y 0 - trajectory B (Y 0) 0‖ ≤ (0 : ℝ) := by
    have he : (0 : ℂ) • B = 0 := by ext w j; simp
    change ‖Y 0 - exp ((0 : ℂ) • B) (Y 0)‖ ≤ 0
    rw [he, exp_zero]
    simp
  have hb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖C t (Y t) - B (trajectory B (Y 0) t)‖ ≤
        M * ‖Y t - trajectory B (Y 0) t‖ + (ε * K) * ‖Y 0‖ := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have he : C t (Y t) - B (trajectory B (Y 0) t) =
        C t (Y t - trajectory B (Y 0) t) + (C t - B) (trajectory B (Y 0) t) := by
      simp only [map_sub, sub_apply, sub_add_sub_cancel]
    have htB : ‖trajectory B (Y 0) t‖ ≤ K * ‖Y 0‖ :=
      ((flow B t).le_opNorm (Y 0)).trans
        (mul_le_mul_of_nonneg_right (hF t ht') (norm_nonneg _))
    rw [he]
    calc
      _ ≤ ‖C t (Y t - trajectory B (Y 0) t)‖ + ‖(C t - B) (trajectory B (Y 0) t)‖ :=
        norm_add_le _ _
      _ ≤ ‖C t‖ * ‖Y t - trajectory B (Y 0) t‖ + ‖C t - B‖ * ‖trajectory B (Y 0) t‖ :=
        add_le_add ((C t).le_opNorm _) ((C t - B).le_opNorm _)
      _ ≤ M * ‖Y t - trajectory B (Y 0) t‖ + ε * (K * ‖Y 0‖) :=
        add_le_add (mul_le_mul_of_nonneg_right (hC t ht') (norm_nonneg _))
          (mul_le_mul (hE t ht') htB (norm_nonneg _) hε)
      _ = _ := by ring
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd hinit hb t ht
  have hmono := gronwallBound_mono (δ := 0) (show (0 : ℝ) ≤ 0 from le_rfl)
    (mul_nonneg (mul_nonneg hε hK) (norm_nonneg (Y 0))) hM ht.2
  have htotal := hg.trans (by simpa only [sub_zero] using hmono)
  rwa [gronwall_zero_mul] at htotal

/-- The actual shifted solution becomes uniformly relatively close to its
limiting constant-system trajectory, without constructing a fundamental matrix. -/
theorem eventual_relative_error {n : ℕ} {A : ℝ → Operator n} {B : Operator n}
    {Y : ℝ → State n} (hlim : Tendsto A atTop (𝓝 B))
    (hode : ∀ᶠ r : ℝ in atTop, HasDerivAt Y (A r (Y r)) r) :
    ∀ δ > 0, ∀ᶠ r : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ‖Y (r + t) - trajectory B (Y r) t‖ ≤ δ * ‖Y r‖ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (flow_continuous B).continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by constructor <;> norm_num))
  let M : ℝ := ‖B‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : ∀ᶠ r : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖A (r + t)‖ ≤ M := by
    apply (eventually_shift_error_lt hlim (show (0 : ℝ) < 1 by norm_num)).mono
    intro r hr t ht
    have hn := norm_add_le (A (r + t) - B) B
    simp only [sub_add_cancel] at hn
    dsimp [M]
    linarith [hr t ht]
  have hshift : ∀ᶠ r : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => Y (r + s)) (A (r + t) (Y (r + t))) t := by
    obtain ⟨R, hR⟩ := eventually_atTop.mp hode
    filter_upwards [eventually_ge_atTop R] with r hr t ht
    have hd := hR (r + t) (by linarith [ht.1])
    convert! hd.scomp t ((hasDerivAt_id t).const_add r) using 1
    simp only [one_smul]
  intro δ hδ
  have hc : Continuous (fun e : ℝ => gronwallBound 0 M (e * K) 1) :=
    (gronwallBound_continuous_ε 0 M 1).comp (continuous_id.mul continuous_const)
  have hneigh : ∀ᶠ e : ℝ in 𝓝 0, gronwallBound 0 M (e * K) 1 < δ := by
    apply hc.continuousAt.eventually_lt_const
    simpa only [zero_mul, gronwallBound_ε0_δ0] using hδ
  obtain ⟨η, hη, heta⟩ := Metric.eventually_nhds_iff.mp hneigh
  have hep : 0 < η / 2 := by positivity
  have hsmall : gronwallBound 0 M ((η / 2) * K) 1 < δ :=
    heta (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hep] using
      (show η / 2 < η by linarith))
  filter_upwards [hshift, hC, eventually_shift_error_lt hlim hep] with r hr hCr hEr t ht
  have hh := trajectory_error_bound hM hK0 hep.le hr hCr (fun t ht => (hEr t ht).le) hK t ht
  simp only [add_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg (Y r)))

/-- Actual scalar window lower bound from coefficient convergence and the
actual solution ODE alone. There is no supplied flow, observability premise,
or integrable coefficient-error assumption. -/
theorem actual_companion_scalar_window {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {A : ℝ → Operator n} {Y : ℝ → State n}
    (hlim : Tendsto A atTop (𝓝 (ζ • companion b)))
    (hode : ∀ᶠ r : ℝ in atTop, HasDerivAt Y (A r (Y r)) r) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ r : ℝ in atTop,
      ∃ t ∈ Icc (0 : ℝ) 1, a * ‖Y r‖ ≤ ‖Y (r + t) 0‖ := by
  obtain ⟨c, hc, hobs⟩ := exists_observation_bound hζ (rotated_companion_shiftRows b ζ)
  refine ⟨c / 2, by positivity, ?_⟩
  apply (eventual_relative_error hlim hode (c / 2) (by positivity)).mono
  intro r hr
  obtain ⟨t, ht, hw⟩ := hobs (Y r)
  refine ⟨t, ht, ?_⟩
  have hd : ‖trajectory (ζ • companion b) (Y r) t 0 - Y (r + t) 0‖ ≤ (c / 2) * ‖Y r‖ := by
    calc
      _ ≤ ‖trajectory (ζ • companion b) (Y r) t - Y (r + t)‖ := norm_le_pi_norm _ _
      _ = ‖Y (r + t) - trajectory (ζ • companion b) (Y r) t‖ := norm_sub_rev _ _
      _ ≤ _ := hr t ht
  have htri : ‖trajectory (ζ • companion b) (Y r) t 0‖ ≤
      ‖trajectory (ζ • companion b) (Y r) t 0 - Y (r + t) 0‖ + ‖Y (r + t) 0‖ := by
    simpa using norm_add_le
      (trajectory (ζ • companion b) (Y r) t 0 - Y (r + t) 0) (Y (r + t) 0)
  linarith

#print axioms eventual_relative_error
#print axioms actual_companion_scalar_window

end V10.CompanionScalarWindow
