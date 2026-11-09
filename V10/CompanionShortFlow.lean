import V10.CompanionObservation
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniform short-interval limits of actual fundamental matrices

Coefficient convergence on a half-line implies uniform convergence of the
unit-time fundamental matrices to the limiting exponential. Gronwall proves
the matrix error estimate from actual ODE derivatives and normalization.
-/

noncomputable section
open Set Filter NormedSpace
open scoped Topology
namespace V10.CompanionShortFlow
open V10.CompanionObservation
set_option backward.isDefEq.respectTransparency false

abbrev Operator (n : ℕ) := State n →L[ℂ] State n

local instance {n : ℕ} : NormedAlgebra ℚ (Operator n) := .restrictScalars ℚ ℂ _

def flow {n : ℕ} (B : Operator n) (t : ℝ) : Operator n := exp ((t : ℂ) • B)

theorem flow_hasDerivAt {n : ℕ} (B : Operator n) (t : ℝ) :
    HasDerivAt (flow B) (B * flow B t) t := by
  have h := hasDerivAt_exp_smul_const' B (t : ℂ)
  convert! h.scomp t Complex.ofRealCLM.hasDerivAt using 1
  simp only [flow, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]

theorem flow_continuous {n : ℕ} (B : Operator n) : Continuous (flow B) :=
  continuous_iff_continuousAt.mpr fun t => (flow_hasDerivAt B t).continuousAt

/-- The error of actual normalized matrix trajectories is controlled by
the coefficient error, uniformly throughout the observation interval. -/
theorem flow_error_bound {n : ℕ} {B : Operator n} {C X : ℝ → Operator n}
    {M K ε : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt X (C t * X t) t) (hzero : X 0 = 1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t‖ ≤ M)
    (hE : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t - B‖ ≤ ε)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ‖flow B t‖ ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖X t - flow B t‖ ≤ gronwallBound 0 M (ε * K) 1 := by
  have hcX : ContinuousOn X (Icc (0 : ℝ) 1) :=
    fun t ht => (hX t ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t => X t - flow B t) (Icc (0 : ℝ) 1) :=
    hcX.sub (flow_continuous B).continuousOn
  have hd : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun t => X t - flow B t)
        (C t * X t - B * flow B t) (Ici t) t :=
    fun t ht => ((hX t (Ico_subset_Icc_self ht)).sub (flow_hasDerivAt B t)).hasDerivWithinAt
  have hinit : ‖X 0 - flow B 0‖ ≤ (0 : ℝ) := by
    have he : (0 : ℂ) • B = 0 := by ext w j; simp
    change ‖X 0 - exp ((0 : ℂ) • B)‖ ≤ 0
    rw [hzero, he, exp_zero, sub_self, norm_zero]
  have hb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖C t * X t - B * flow B t‖ ≤ M * ‖X t - flow B t‖ + ε * K := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have he : C t * X t - B * flow B t =
        C t * (X t - flow B t) + (C t - B) * flow B t := by
      rw [mul_sub, sub_mul, sub_add_sub_cancel]
    rw [he]
    calc
      _ ≤ ‖C t * (X t - flow B t)‖ + ‖(C t - B) * flow B t‖ := norm_add_le _ _
      _ ≤ ‖C t‖ * ‖X t - flow B t‖ + ‖C t - B‖ * ‖flow B t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * ‖X t - flow B t‖ + ε * K :=
        add_le_add (mul_le_mul_of_nonneg_right (hC t ht') (norm_nonneg _))
          (mul_le_mul (hE t ht') (hF t ht') (norm_nonneg _) hε)
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd hinit hb t ht
  exact hg.trans (by simpa using (gronwallBound_mono (δ := 0) (show (0 : ℝ) ≤ 0 from le_rfl)
    (mul_nonneg hε hK) hM ht.2))

/-- A half-line coefficient limit is uniform over all forward shifts in [0,1]. -/
theorem eventually_shift_error_lt {n : ℕ} {A : ℝ → Operator n} {B : Operator n}
    (hlim : Tendsto A atTop (𝓝 B)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖A (r + t) - B‖ < ε := by
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp hlim ε hε
  filter_upwards [eventually_ge_atTop R] with r hr t ht
  simpa only [dist_eq_norm] using hR (r + t) (by linarith [ht.1])

/-- Actual normalized short-interval matrix solutions converge uniformly
to the limiting exponential. There is no integrability/rate assumption on
the coefficient perturbation. -/
theorem actual_flow_uniform_limit {n : ℕ} {A : ℝ → Operator n} {B : Operator n}
    {X : ℝ → ℝ → Operator n} (hlim : Tendsto A atTop (𝓝 B))
    (hode : ∀ᶠ r : ℝ in atTop, X r 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (X r) (A (r + t) * X r t) t) :
    ∀ δ > 0, ∀ᶠ r : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ‖X r t - flow B t‖ < δ := by
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
  filter_upwards [hode, hC, eventually_shift_error_lt hlim hep] with r hr hCr hEr t ht
  exact (flow_error_bound hM hK0 hep.le hr.2 hr.1 hCr
    (fun t ht => (hEr t ht).le) hK t ht).trans_lt hsmall

/-- Combining actual coefficient convergence with actual companion observation
gives a uniform positive scalar observation constant for all late intervals. -/
theorem eventual_companion_observation {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) {A : ℝ → Operator n} {X : ℝ → ℝ → Operator n}
    (hlim : Tendsto A atTop (𝓝 (ζ • companion b)))
    (hode : ∀ᶠ r : ℝ in atTop, X r 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (X r) (A (r + t) * X r t) t) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ r : ℝ in atTop,
      ∀ w : State n, ∃ t ∈ Icc (0 : ℝ) 1, a * ‖w‖ ≤ ‖X r t w 0‖ := by
  obtain ⟨a, ha, hobs⟩ := companion_stable_observation b hζ
  refine ⟨a, ha, ?_⟩
  apply (actual_flow_uniform_limit hlim hode a ha).mono
  intro r hr
  exact hobs (X r) (fun t ht => (hr t ht).le)

#print axioms actual_flow_uniform_limit
#print axioms eventual_companion_observation

end V10.CompanionShortFlow
