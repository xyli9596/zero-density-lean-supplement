import V10.BoundedCoefficientZeroCount
import V10.ScaledDivisorCount

/-! Actual affine rescaling of a scalar ODE, its derivative jet and its divisor.
This converts a coefficient bound in powers of a local scale into the physical
unit-disk zero bound needed for Lemma 4.1. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace V10.AffineScalarZeroCount
open ZeroDensity.ScalarLimit BoundedCoefficientZeroCount RadialTransfer

/-- All actual scalar derivatives under an affine coordinate change. -/
theorem iteratedDeriv_affine {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (c k : ℂ) (j : ℕ) (ζ : ℂ) :
    iteratedDeriv j (fun z => f (c + k * z)) ζ = k ^ j * iteratedDeriv j f (c + k * ζ) := by
  have hc : ContDiff ℂ j (fun z => f (c + z)) :=
    contDiff_iff_contDiffAt.mpr fun z =>
      ((hf _ (mem_univ _)).comp (analyticAt_const.add analyticAt_id)).contDiffAt
  have hh := congrFun (iteratedDeriv_comp_const_mul hc k) ζ
  simpa only [iteratedDeriv_comp_const_add] using hh

/-- Affine rescaling gives exactly the rescaled monic scalar equation. -/
theorem scalar_equation_affine {n : ℕ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {b : ℂ → Fin (n + 1) → ℂ}
    (hs : ∀ z, iteratedDeriv (n + 1) f z + ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val f z = 0)
    (c k ζ : ℂ) :
    iteratedDeriv (n + 1) (fun z => f (c + k * z)) ζ +
      ∑ j : Fin (n + 1), (k ^ (n + 1 - j.val) * b (c + k * ζ) j) *
        iteratedDeriv j.val (fun z => f (c + k * z)) ζ = 0 := by
  simp_rw [iteratedDeriv_affine hf]
  calc
    _ = k ^ (n + 1) * (iteratedDeriv (n + 1) f (c + k * ζ) +
        ∑ j : Fin (n + 1), b (c + k * ζ) j * iteratedDeriv j.val f (c + k * ζ)) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hp : k ^ (n + 1 - j.val) * k ^ j.val = k ^ (n + 1) := by
        rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
      calc
        _ = (k ^ (n + 1 - j.val) * k ^ j.val) *
            (b (c + k * ζ) j * iteratedDeriv j.val f (c + k * ζ)) := by ring
        _ = _ := by rw [hp]
    _ = 0 := by rw [hs, mul_zero]

theorem jet_affine_ne_zero {n : ℕ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {c k : ℂ} (hk : k ≠ 0) (hne : jet n f c ≠ 0) :
    jet n (fun z => f (c + k * z)) 0 ≠ 0 := by
  intro hz
  apply hne
  ext j
  have hj := congrFun hz j
  simp only [jet, iteratedDeriv_affine hf, mul_zero, add_zero, Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ hk)

/-- Actual divisor transport under an affine map with nonzero derivative. -/
theorem regionCount_affine {f : ℂ → ℂ} {U K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (c k : ℂ) (hk : k ≠ 0)
    (hm : MapsTo (fun z => c + k * z) K U) :
    regionCount (fun z => f (c + k * z)) K K =
      regionCount f U ((fun z => c + k * z) '' K) := by
  have hinj : InjOn (fun z => c + k * z) K := by
    intro x hx y hy he
    exact mul_left_cancel₀ hk (add_left_cancel he)
  rw [regionCount_eq_mem_sum, regionCount_eq_mem_sum, finsum_mem_image hinj]
  congr 1
  apply finsum_mem_congr rfl
  intro z hz
  exact ZeroDensity.ConformalMultiplicity.divisor_comp hf
    (fun z _ => analyticAt_const.add (analyticAt_const.mul analyticAt_id)) hm hz
    (by
      change deriv (fun w => c + k * w) z ≠ 0
      have hd : HasDerivAt (fun w : ℂ => c + k * w) k z := by
        simpa using ((hasDerivAt_id z).const_mul k).const_add c
      rwa [hd.deriv])

theorem image_affine_closedBall {L : ℝ} (hL : 0 < L) (c : ℂ) :
    (fun ζ : ℂ => c + (L : ℂ)⁻¹ * ζ) '' closedBall 0 L = closedBall c 1 := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  ext w
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    calc
      L⁻¹ * ‖ζ‖ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hζ)
        (inv_nonneg.mpr hL.le)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  · intro hw
    refine ⟨(L : ℂ) * (w - c), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      exact (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hw)
        hL.le).trans_eq (mul_one L)
    · dsimp only
      rw [← mul_assoc, inv_mul_cancel₀ hLc, one_mul, add_sub_cancel]

/-- Actual unit-disk bound from a local coefficient estimate in powers of L.
The radius and coefficient scale are coupled by the exact affine derivative
formula, and the original physical divisor is the conclusion. -/
theorem unit_disk_divisor_le {n : ℕ} {f : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ z, iteratedDeriv (n + 1) f z + ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val f z = 0)
    {c : ℂ} {L B : ℝ} (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ w ∈ closedBall c 5, ∀ j, ‖b w j‖ ≤ B * L ^ (n + 1 - j.val))
    (hne : jet (n + 1) f c ≠ 0) :
    ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c 1) z : ℤ) : ℝ) ≤
      diskCountConstant (n + 1) (1 + (n + 1 : ℝ) * B) * L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let k : ℂ := (L : ℂ)⁻¹
  have hk : k ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hLp.ne')
  let g := fun ζ : ℂ => f (c + k * ζ)
  have hg : AnalyticOnNhd ℂ g univ :=
    fun ζ _ => (hf _ (mem_univ _)).comp (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hb' : ∀ ζ ∈ closedBall 0 (5 * L), ∀ j : Fin (n + 1),
      ‖k ^ (n + 1 - j.val) * b (c + k * ζ) j‖ ≤ B := by
    intro ζ hζ j
    have hkw : ‖k‖ = L⁻¹ := by simp [k, abs_of_pos hLp]
    have hm : c + k * ζ ∈ closedBall c 5 := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hkw]
      calc
        _ ≤ L⁻¹ * (5 * L) := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hζ)
          (inv_nonneg.mpr hLp.le)
        _ = 5 := by field_simp
    rw [norm_mul, norm_pow, hkw]
    calc
      _ ≤ (L⁻¹) ^ (n + 1 - j.val) * (B * L ^ (n + 1 - j.val)) :=
        mul_le_mul_of_nonneg_left (hb _ hm j) (by positivity)
      _ = B := by rw [inv_pow]; field_simp
  have hcount := disk_divisor_le_of_scalar_ode hL hB (hg.mono (subset_univ _))
    (fun ζ _ => scalar_equation_affine hf hs c k ζ) hb' (jet_affine_ne_zero hf hk hne)
  have himg := image_affine_closedBall hLp c
  have hmap : MapsTo (fun ζ => c + k * ζ) (closedBall 0 L) (closedBall c 1) := by
    intro ζ hζ
    rw [← himg]
    exact mem_image_of_mem _ hζ
  have he := regionCount_affine (hf.mono (subset_univ (closedBall c 1))) c k hk hmap
  rw [himg] at he
  have hcg : regionCount g (closedBall 0 L) (closedBall 0 L) =
      ((∑ᶠ z, MeromorphicOn.divisor g (closedBall 0 L) z : ℤ) : ℝ) := by
    unfold regionCount
    congr 1
    apply finsum_congr
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) L <;> simp [hz]
  have hcf : regionCount f (closedBall c 1) (closedBall c 1) =
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c 1) z : ℤ) : ℝ) := by
    unfold regionCount
    congr 1
    apply finsum_congr
    intro z
    by_cases hz : z ∈ closedBall c 1 <;> simp [hz]
  rw [hcg, hcf] at he
  rw [← he]
  exact hcount

#print axioms unit_disk_divisor_le
end V10.AffineScalarZeroCount
