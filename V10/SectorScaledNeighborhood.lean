import V10.PerronSector
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Scaled local neighborhoods in a sector

The full angular cone is the exponential image of the entire logarithmic
strip. Local logarithmic rectangles avoid any principal-argument branch cut.
Uniform convergence on compact angle sets then gives a uniform coefficient
bound and eventual inclusion of every scaled point of one open disk in the
original exterior sector.
-/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace V10.SectorScaledNeighborhood
open PerronSector

def fullCone (J : Set ℝ) : Set ℂ :=
  Complex.exp '' {w : ℂ | w.im ∈ J}

theorem fullCone_isOpen {J : Set ℝ} (hJ : IsOpen J) : IsOpen (fullCone J) :=
  Complex.isOpenMap_exp _ (hJ.preimage Complex.continuous_im)

theorem fullCone_ne_zero {J : Set ℝ} {z : ℂ} (hz : z ∈ fullCone J) : z ≠ 0 := by
  obtain ⟨w, _, rfl⟩ := hz
  exact Complex.exp_ne_zero w

theorem sector_subset_fullCone (R : ℝ) (J : Set ℝ) : sector R J ⊆ fullCone J := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, hw.2, rfl⟩

/-- Every point in the full cone has one open disk on which all scaled-domain,
uniform-bound, and radial-limit hypotheses are derived from the manuscript's
uniform convergence on compact angle intervals. -/
theorem exists_scaled_disk {F : Type*} [NormedAddCommGroup F]
    {A : ℂ → F} {A₀ : F} {R₀ : ℝ} {J : Set ℝ} {ζ : ℂ}
    (hR₀ : 0 < R₀) (hJ : IsOpen J) (hζ : ζ ∈ fullCone J)
    (hlim : ∀ K : Set ℝ, K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => A₀) atTop K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ≥0,
      ball ζ ε ⊆ fullCone J ∧
      (∀ z ∈ ball ζ ε, z ≠ 0) ∧
      (∀ᶠ R : ℝ in atTop, ∀ z ∈ ball ζ ε, (R : ℂ) * z ∈ sector R₀ J) ∧
      (∀ᶠ R : ℝ in atTop, ∀ z ∈ ball ζ ε, ‖A ((R : ℂ) * z)‖ ≤ M) ∧
      (∀ z ∈ ball ζ ε, Tendsto (fun R : ℝ => A ((R : ℂ) * z)) atTop (𝓝 A₀)) := by
  obtain ⟨w, hwJ, hwζ⟩ := hζ
  obtain ⟨d, hd, hdJ⟩ := Metric.isOpen_iff.mp hJ w.im hwJ
  let K : Set ℝ := closedBall w.im (d / 2)
  have hKJ : K ⊆ J := by
    intro θ hθ
    apply hdJ
    exact lt_of_le_of_lt (mem_closedBall.mp hθ) (by linarith)
  have hK : IsCompact K := isCompact_closedBall w.im (d / 2)
  let U : Set ℂ := {u | (w.re - 1 < u.re ∧ u.re < w.re + 1) ∧
    u.im ∈ ball w.im (d / 2)}
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_ball.preimage Complex.continuous_im)
  have hwU : w ∈ U := ⟨⟨by linarith, by linarith⟩, mem_ball_self (by positivity)⟩
  have hζU : ζ ∈ Complex.exp '' U := ⟨w, hwU, hwζ⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (Complex.isOpenMap_exp _ hU) ζ hζU
  have hpolar : ∀ z ∈ ball ζ ε, ∃ ρ : ℝ, Real.exp (w.re - 1) < ρ ∧
      ∃ θ ∈ K, z = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hεU hz
    refine ⟨Real.exp u.re, Real.exp_lt_exp.mpr hu.1.1, u.im,
      ball_subset_closedBall hu.2, ?_⟩
    conv_lhs => rw [← Complex.re_add_im u]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
  have hm : 0 < Real.exp (w.re - 1) := Real.exp_pos _
  have hsub : ball ζ ε ⊆ fullCone J := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hεU hz
    exact ⟨u, hKJ (ball_subset_closedBall hu.2), rfl⟩
  have hcoord : Tendsto (fun R : ℝ => R * Real.exp (w.re - 1)) atTop atTop :=
    tendsto_id.atTop_mul_const hm
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ ball ζ ε, (R : ℂ) * z ∈ sector R₀ J := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hcoord.eventually (eventually_gt_atTop R₀)]
      with R hR hRR z hz
    obtain ⟨ρ, hρ, θ, hθ, rfl⟩ := hpolar z hz
    have hrad : R₀ < R * ρ := hRR.trans_le (mul_le_mul_of_nonneg_left hρ.le hR.le)
    simpa only [Complex.ofReal_mul, mul_assoc] using ray_mem_sector hR₀ hrad (hKJ hθ)
  let M : ℝ≥0 := ⟨‖A₀‖ + 1, by positivity⟩
  have hdist := (Metric.tendstoUniformlyOn_iff.mp (hlim K hKJ hK)) 1 zero_lt_one
  obtain ⟨T, hT⟩ := eventually_atTop.mp hdist
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ z ∈ ball ζ ε, ‖A ((R : ℂ) * z)‖ ≤ M := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hcoord.eventually (eventually_ge_atTop T)]
      with R hR hRT z hz
    obtain ⟨ρ, hρ, θ, hθ, rfl⟩ := hpolar z hz
    have hrad : T ≤ R * ρ := hRT.trans (mul_le_mul_of_nonneg_left hρ.le hR.le)
    have hd' := hT (R * ρ) hrad θ hθ
    simp only [Complex.ofReal_mul, mul_assoc, dist_eq_norm] at hd'
    rw [norm_sub_rev] at hd'
    have ht := norm_add_le (A ((R : ℂ) * ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) - A₀) A₀
    rw [sub_add_cancel] at ht
    change _ ≤ ‖A₀‖ + 1
    linarith
  refine ⟨ε, hε, M, hsub, fun z hz => fullCone_ne_zero (hsub hz), hmap, hbound, ?_⟩
  intro z hz
  obtain ⟨ρ, hρ, θ, hθ, rfl⟩ := hpolar z hz
  have hρpos : 0 < ρ := hm.trans hρ
  have ht := ((hlim K hKJ hK).tendsto_at hθ).comp (tendsto_id.atTop_mul_const hρpos)
  simpa only [Function.comp_def, id_eq, Complex.ofReal_mul, mul_assoc] using ht

/-- The open-convex-neighborhood interface used by the global scalar limit
theorem. Every condition follows from the sector assumptions above. -/
theorem exists_scaled_neighborhood {F : Type*} [NormedAddCommGroup F]
    {A : ℂ → F} {A₀ : F} {R₀ : ℝ} {J : Set ℝ}
    (hR₀ : 0 < R₀) (hJ : IsOpen J)
    (hlim : ∀ K : Set ℝ, K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => A₀) atTop K) :
    ∀ ζ ∈ fullCone J, ∃ N : Set ℂ, IsOpen N ∧ ζ ∈ N ∧ N ⊆ fullCone J ∧
      Convex ℝ N ∧ (∀ z ∈ N, z ≠ 0) ∧ ∃ M : ℝ≥0,
      (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, (R : ℂ) * z ∈ sector R₀ J) ∧
      (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, ‖A ((R : ℂ) * z)‖ ≤ M) ∧
      (∀ z ∈ N, Tendsto (fun R : ℝ => A ((R : ℂ) * z)) atTop (𝓝 A₀)) := by
  intro ζ hζ
  obtain ⟨ε, hε, M, hsub, hne, hmap, hbound, hpoint⟩ := exists_scaled_disk hR₀ hJ hζ hlim
  exact ⟨ball ζ ε, isOpen_ball, mem_ball_self hε, hsub, convex_ball ζ ε, hne,
    M, hmap, hbound, hpoint⟩

#print axioms exists_scaled_disk
#print axioms exists_scaled_neighborhood

end V10.SectorScaledNeighborhood
