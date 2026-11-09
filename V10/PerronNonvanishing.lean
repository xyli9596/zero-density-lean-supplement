import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! A nonzero holomorphic solution of a homogeneous linear system never vanishes
as a vector on its connected open domain. The coefficient needs only continuity;
local uniqueness is proved with Gronwall on actual line segments. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.PerronNonvanishing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Local uniqueness from the actual ODE: a zero value forces vanishing on a ball. -/
theorem zero_on_ball {S : Set ℂ} {A : ℂ → E →L[ℂ] E} {Y : ℂ → E}
    (hA : ContinuousOn A S)
    (hY : ∀ z ∈ S, HasDerivAt Y (A z (Y z)) z)
    {z₀ : ℂ} {r : ℝ} (_hr : 0 < r) (hball : ball z₀ r ⊆ S) (hzero : Y z₀ = 0) :
    ∀ z ∈ ball z₀ r, Y z = 0 := by
  intro z hz
  let d : ℂ := z - z₀
  let path : ℝ → ℂ := fun t => z₀ + (t : ℂ) * d
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ S := by
    intro t ht
    apply hball
    have hd : ‖d‖ < r := by simpa [d, dist_eq_norm] using hz
    have ht0 : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_nonneg ht.1]
    rw [mem_ball, dist_eq_norm]
    dsimp [path]
    rw [add_sub_cancel_left, norm_mul, ht0]
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2).trans_lt hd
  have hpc : Continuous path := by dsimp [path]; fun_prop
  have hcont : ContinuousOn Y S := fun z hz => (hY z hz).continuousAt.continuousWithinAt
  have hf : ContinuousOn (fun t => Y (path t)) (Icc (0 : ℝ) 1) :=
    hcont.comp hpc.continuousOn hpath
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Y (path t)) (d • A (path t) (Y (path t))) t := by
    have hp : HasDerivAt (fun w : ℂ => z₀ + w * d) d (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const d).const_add z₀
    exact (hY (path t) (hpath t ht)).scomp t hp.comp_ofReal
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.comp hpc.continuousOn hpath)
  have hh := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (K := ‖d‖ * C) hf
    (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simpa [path] using hzero)
    (fun t ht => calc
      ‖d • A (path t) (Y (path t))‖ = ‖d‖ * ‖A (path t) (Y (path t))‖ := norm_smul _ _
      _ ≤ ‖d‖ * (‖A (path t)‖ * ‖Y (path t)‖) :=
        mul_le_mul_of_nonneg_left ((A (path t)).le_opNorm _) (norm_nonneg _)
      _ ≤ (‖d‖ * C) * ‖Y (path t)‖ := by
        have hb := hC t (Ico_subset_Icc_self ht)
        exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg (Y (path t))))
          (norm_nonneg d)).trans_eq (mul_assoc _ _ _).symm)
  simpa [path, d] using hh 1 (by constructor <;> norm_num)

/-- One zero forces the solution to be identically zero on the connected domain. -/
theorem eqOn_zero_of_eq_zero {S : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} (hA : ContinuousOn A S)
    (hY : ∀ z ∈ S, HasDerivAt Y (A z (Y z)) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hzero : Y z₀ = 0) : Set.EqOn Y 0 S := by
  have han : AnalyticOnNhd ℂ Y S :=
    (show DifferentiableOn ℂ Y S from fun z hz =>
      (hY z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hS
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS z₀ hz₀
  have hevent : Y =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact zero_on_ball hA hY hr hball hzero z hz
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hevent

/-- A genuinely nonzero solution is nowhere zero as a vector; no ray-wise
nonvanishing assumption is required. -/
theorem nowhere_zero {S : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} (hA : ContinuousOn A S)
    (hY : ∀ z ∈ S, HasDerivAt Y (A z (Y z)) z)
    (hnonzero : ∃ z ∈ S, Y z ≠ 0) : ∀ z ∈ S, Y z ≠ 0 := by
  intro z hz hzero
  obtain ⟨w, hw, hn⟩ := hnonzero
  exact hn (eqOn_zero_of_eq_zero hS hconn hA hY hz hzero hw)

end V10.PerronNonvanishing
