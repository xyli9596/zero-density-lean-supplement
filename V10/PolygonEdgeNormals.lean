import V10.LocalSupportFace
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! A canonical, non-redundant finite set of actual positive polygon edge
normals. The half-open interval includes the negative-real normal exactly once. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace V10.PolygonEdgeNormals
open ZeroDensity PolygonFaces

def weight (s : Finset ℂ) (θ : ℝ) : ℝ :=
  MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ

theorem weight_nonneg (s : Finset ℂ) (θ : ℝ) : 0 ≤ weight s θ := Metric.diam_nonneg

theorem positive_normals_finite (s : Finset ℂ) (hs : s.Nonempty) :
    {θ | θ ∈ Ioc (-Real.pi) Real.pi ∧ 0 < weight s θ}.Finite := by
  apply (positive_faces_finite s hs (-Real.pi - 1) (Real.pi + 1)).subset
  rintro θ ⟨hθ, hd⟩
  exact ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hd⟩

def normals (s : Finset ℂ) (hs : s.Nonempty) : Finset ℝ :=
  (positive_normals_finite s hs).toFinset

theorem mem_normals {s : Finset ℂ} {hs : s.Nonempty} {θ : ℝ} :
    θ ∈ normals s hs ↔ θ ∈ Ioc (-Real.pi) Real.pi ∧ 0 < weight s θ := by
  simp [normals]

theorem weight_eq_zero_of_notMem {s : Finset ℂ} {hs : s.Nonempty} {θ : ℝ}
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) (hn : θ ∉ normals s hs) : weight s θ = 0 := by
  apply le_antisymm _ (weight_nonneg s θ)
  by_contra! hp
  exact hn (mem_normals.mpr ⟨hθ, hp⟩)

theorem arg_unitPoint {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    Complex.arg (Complex.exp ((θ : ℂ) * Complex.I)) = θ := by
  rw [Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  simpa only [neg_add_cancel_left, two_mul] using hθ

theorem unitPoint_injective :
    InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (Ioc (-Real.pi) Real.pi) := by
  intro θ hθ α hα he
  have h := congrArg Complex.arg he
  rwa [arg_unitPoint hθ, arg_unitPoint hα] at h

theorem weight_eq_of_exp_eq (s : Finset ℂ) {θ α : ℝ}
    (he : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((α : ℂ) * Complex.I)) :
    weight s θ = weight s α := by
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hc : Real.cos θ = Real.cos α := by simpa [Complex.exp_re] using hre
  have hs : Real.sin θ = Real.sin α := by simpa [Complex.exp_im] using him
  unfold weight MainTheorem.faceLength
  rw [actualFace_eq, actualFace_eq]
  simp only [normalLinear, hc, hs]

theorem normal_ray_self (r θ : ℝ) :
    normalLinear θ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = r := by
  have he : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  simp only [normalLinear, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have h : Real.cos θ * (r * Real.cos θ) + Real.sin θ * (r * Real.sin θ) = r := by
    calc
      _ = r * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r := by rw [he, mul_one]
  simpa [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im] using h

/-- The local hinge form at an arbitrary nonzero point, with its canonical
angle and the actual nonnegative Euclidean edge weight. -/
theorem support_local_hinge (s : Finset ℂ) (hs : s.Nonempty)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ p ∈ s, ∀ᶠ z in 𝓝 z₀,
      LocalSupportFace.support s hs z = LocalSupportFace.projection p z +
        weight s z₀.arg * max 0 (angularTangent z₀.arg z) := by
  obtain ⟨p, hp, q, hq, _, _, _, he⟩ :=
    LocalSupportFace.support_eventually_hinge s hs (norm_pos_iff.mpr hz₀) z₀.arg
  rw [Complex.norm_mul_exp_arg_mul_I] at he
  exact ⟨p, hp, he⟩

#print axioms positive_normals_finite
#print axioms support_local_hinge
end V10.PolygonEdgeNormals
