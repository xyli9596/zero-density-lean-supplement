import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Short-interval observation for companion systems

The shift rows of a companion operator make its first coordinate observable.
We prove injectivity of the actual exponential observation map by differentiating
on the interior of [0,1], then obtain a positive uniform norm lower bound from
finite dimensionality. No observability inequality is assumed.
-/

noncomputable section
open Set Filter NormedSpace
open scoped Topology

namespace V10.CompanionObservation
set_option backward.isDefEq.respectTransparency false

abbrev State (n : ℕ) := Fin (n + 1) → ℂ
abbrev Time := Icc (0 : ℝ) 1

/-- The rows shared by every rotated companion matrix. Its final row is
unrestricted, and the rotation need only be nonzero. -/
def ShiftRows {n : ℕ} (B : State n →L[ℂ] State n) (ζ : ℂ) : Prop :=
  ∀ w (j : Fin n), B w j.castSucc = ζ * w j.succ

/-- The actual companion operator for `v^(n+1) + ∑ b_j v^(j) = 0`,
with shift rows followed by the negative coefficient row. -/
def companion {n : ℕ} (b : Fin (n + 1) → ℂ) : State n →L[ℂ] State n :=
  ContinuousLinearMap.pi fun i => Fin.lastCases
    (-∑ j : Fin (n + 1), b j • (ContinuousLinearMap.proj j : State n →L[ℂ] ℂ))
    (fun j : Fin n => ContinuousLinearMap.proj j.succ) i

theorem companion_last {n : ℕ} (b : Fin (n + 1) → ℂ) (w : State n) :
    companion b w (Fin.last n) = -∑ j, b j * w j := by
  simp [companion]

theorem rotated_companion_shiftRows {n : ℕ} (b : Fin (n + 1) → ℂ) (ζ : ℂ) :
    ShiftRows (ζ • companion b) ζ := by
  intro w j
  simp [companion]

def trajectory {n : ℕ} (B : State n →L[ℂ] State n) (w : State n) (t : ℝ) : State n :=
  exp ((t : ℂ) • B) w

theorem trajectory_hasDerivAt {n : ℕ} (B : State n →L[ℂ] State n)
    (w : State n) (t : ℝ) :
    HasDerivAt (trajectory B w) (B (trajectory B w t)) t := by
  have h := (hasDerivAt_exp_smul_const' B (t : ℂ)).clm_apply
    (hasDerivAt_const (t : ℂ) w)
  convert! h.scomp t Complex.ofRealCLM.hasDerivAt using 1
  simp only [trajectory, mul_apply_eq_comp, Complex.ofRealCLM_apply,
    Complex.ofReal_one, one_smul, map_zero, add_zero]

theorem trajectory_continuous {n : ℕ} (B : State n →L[ℂ] State n) (w : State n) :
    Continuous (trajectory B w) :=
  continuous_iff_continuousAt.mpr fun t => (trajectory_hasDerivAt B w t).continuousAt

/-- Vanishing of the first coordinate on an open interval forces every
coordinate to vanish there, by the actual ODE and companion shift rows. -/
theorem all_coordinates_zero_of_first_zero {n : ℕ}
    {B : State n →L[ℂ] State n} {ζ : ℂ} (hζ : ζ ≠ 0) (hB : ShiftRows B ζ)
    {Y : ℝ → State n} (hode : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Y (B (Y t)) t)
    (hzero : ∀ t ∈ Ioo (0 : ℝ) 1, Y t 0 = 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1, Y t = 0 := by
  have hall : ∀ k (hk : k < n + 1), ∀ t ∈ Ioo (0 : ℝ) 1, Y t ⟨k, hk⟩ = 0 := by
    intro k
    induction k with
    | zero => intro hk t ht; exact hzero t ht
    | succ k ih =>
      intro hk t ht
      have hkn : k < n := by omega
      have hkp : k < n + 1 := by omega
      have heq : (fun s => Y s (⟨k, hkp⟩ : Fin (n + 1))) =ᶠ[𝓝 t] 0 := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact ih hkp s hs
      have hd := (hasDerivAt_pi.mp (hode t ht)) (⟨k, hkp⟩ : Fin (n + 1))
      have hd0 := (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq heq
      have he := hd.unique hd0
      have hs := hB (Y t) (⟨k, hkn⟩ : Fin n)
      have hz : ζ * Y t ⟨k + 1, hk⟩ = 0 := by simpa using hs.symm.trans he
      exact (mul_eq_zero.mp hz).resolve_left hζ
  intro t ht
  funext j
  exact hall j.val j.isLt t ht

/-- The actual exponential flow has no kernel at any real time. -/
theorem trajectory_eq_zero_iff {n : ℕ} (B : State n →L[ℂ] State n)
    (w : State n) (t : ℝ) : trajectory B w t = 0 ↔ w = 0 := by
  let : NormedAlgebra ℚ (State n →L[ℂ] State n) := .restrictScalars ℚ ℂ _
  constructor
  · intro hw
    have hinv : exp (-((t : ℂ) • B)) * exp ((t : ℂ) • B) = 1 := by
      rw [← exp_add_of_commute (Commute.refl ((t : ℂ) • B)).neg_left,
        neg_add_cancel, exp_zero]
    have h := congrArg (fun T : State n →L[ℂ] State n => T w) hinv
    change exp (-((t : ℂ) • B)) (trajectory B w t) = w at h
    simpa [hw] using h.symm
  · rintro rfl
    simp [trajectory]

/-- The first-coordinate exponential trajectory, as a continuous function on
the actual observation interval. -/
def observation {n : ℕ} (B : State n →L[ℂ] State n) : State n →ₗ[ℂ] C(Time, ℂ) where
  toFun w := ⟨fun t => trajectory B w t.val 0,
    ((continuous_apply 0).comp (trajectory_continuous B w)).comp continuous_subtype_val⟩
  map_add' u v := by ext t; simp [trajectory]
  map_smul' c w := by ext t; simp [trajectory]

/-- A nonzero rotation of any companion operator has injective observation
on [0,1]. The derivative argument supplies this, rather than assuming it. -/
theorem observation_injective {n : ℕ} {B : State n →L[ℂ] State n} {ζ : ℂ}
    (hζ : ζ ≠ 0) (hB : ShiftRows B ζ) : Function.Injective (observation B) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hfirst : ∀ t ∈ Ioo (0 : ℝ) 1, trajectory B w t 0 = 0 := by
    intro t ht
    have h := congrArg (fun f : C(Time, ℂ) => f ⟨t, ht.1.le, ht.2.le⟩) hw
    exact h
  have hall := all_coordinates_zero_of_first_zero hζ hB
    (fun t _ => trajectory_hasDerivAt B w t) hfirst
  exact (trajectory_eq_zero_iff B w (1 / 2)).mp (hall (1 / 2) (by constructor <;> norm_num))

/-- A continuous function on the compact observation interval attains its norm. -/
theorem observation_norm_attained {n : ℕ} (B : State n →L[ℂ] State n) (w : State n) :
    ∃ t : Time, ‖observation B w‖ = ‖trajectory B w t.val 0‖ := by
  have hne : (univ : Set Time).Nonempty := ⟨⟨0, by constructor <;> norm_num⟩, mem_univ _⟩
  obtain ⟨t, _, hmax⟩ := isCompact_univ.exists_isMaxOn hne (observation B w).continuous.norm.continuousOn
  refine ⟨t, le_antisymm ?_ ((observation B w).norm_coe_le_norm t)⟩
  apply ((observation B w).norm_le (norm_nonneg _)).mpr
  intro s
  exact hmax (mem_univ s)

/-- Literal positive lower observation bound for the actual exponential.
This is the short-interval companion estimate used before scalar L¹ compactness. -/
theorem exists_observation_bound {n : ℕ} {B : State n →L[ℂ] State n} {ζ : ℂ}
    (hζ : ζ ≠ 0) (hB : ShiftRows B ζ) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : State n, ∃ t ∈ Icc (0 : ℝ) 1,
      a * ‖w‖ ≤ ‖trajectory B w t 0‖ := by
  obtain ⟨K, hK, hanti⟩ := (observation B).injective_iff_antilipschitz.mp
    (observation_injective hζ hB)
  have hKr : 0 < (K : ℝ) := hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKr, ?_⟩
  intro w
  obtain ⟨t, ht⟩ := observation_norm_attained B w
  refine ⟨t.val, t.property, ?_⟩
  have hh := hanti.le_mul_dist w 0
  have hn : ‖w‖ ≤ (K : ℝ) * ‖observation B w‖ := by simpa using hh
  rw [← ht]
  calc
    (K : ℝ)⁻¹ * ‖w‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖observation B w‖) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hKr.le)
    _ = ‖observation B w‖ := by rw [← mul_assoc, inv_mul_cancel₀ hKr.ne', one_mul]

/-- The observation estimate persists for any family of operators uniformly
close to the limiting exponential on the actual short interval. -/
theorem exists_stable_observation_bound {n : ℕ} {B : State n →L[ℂ] State n} {ζ : ℂ}
    (hζ : ζ ≠ 0) (hB : ShiftRows B ζ) :
    ∃ a : ℝ, 0 < a ∧ ∀ X : ℝ → State n →L[ℂ] State n,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖X t - exp ((t : ℂ) • B)‖ ≤ a) →
      ∀ w : State n, ∃ t ∈ Icc (0 : ℝ) 1, a * ‖w‖ ≤ ‖X t w 0‖ := by
  obtain ⟨c, hc, hobs⟩ := exists_observation_bound hζ hB
  refine ⟨c / 2, by positivity, ?_⟩
  intro X hX w
  obtain ⟨t, ht, hw⟩ := hobs w
  refine ⟨t, ht, ?_⟩
  have hd : ‖trajectory B w t 0 - X t w 0‖ ≤ (c / 2) * ‖w‖ := by
    calc
      ‖trajectory B w t 0 - X t w 0‖ =
          ‖((exp ((t : ℂ) • B) - X t) w) 0‖ := by rfl
      _ ≤ ‖(exp ((t : ℂ) • B) - X t) w‖ := norm_le_pi_norm _ _
      _ ≤ ‖exp ((t : ℂ) • B) - X t‖ * ‖w‖ :=
        (exp ((t : ℂ) • B) - X t).le_opNorm w
      _ ≤ (c / 2) * ‖w‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (hX t ht) (norm_nonneg w)
  have htri : ‖trajectory B w t 0‖ ≤ ‖trajectory B w t 0 - X t w 0‖ + ‖X t w 0‖ := by
    simpa using norm_add_le (trajectory B w t 0 - X t w 0) (X t w 0)
  linarith

/-- The literal rotated companion instance, with no observability or
injectivity premise. -/
theorem companion_stable_observation {n : ℕ} (b : Fin (n + 1) → ℂ)
    {ζ : ℂ} (hζ : ζ ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ X : ℝ → State n →L[ℂ] State n,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖X t - exp ((t : ℂ) • (ζ • companion b))‖ ≤ a) →
      ∀ w : State n, ∃ t ∈ Icc (0 : ℝ) 1, a * ‖w‖ ≤ ‖X t w 0‖ :=
  exists_stable_observation_bound hζ (rotated_companion_shiftRows b ζ)

#print axioms observation_injective
#print axioms exists_observation_bound
#print axioms companion_stable_observation

end V10.CompanionObservation
