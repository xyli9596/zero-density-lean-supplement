import V10.HomogeneousSubharmonicConvex
import V10.SelectedVertices
import V10.SectorScaledNeighborhood
import ZeroDensity.ConvexSelection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Lemma 3.3: support inequalities from actual subharmonicity

The angular interval is placed in a right half-plane. Positive homogeneity
and the proved maximum-principle theorem give convexity in tangent
coordinates. Local agreement then gives genuine global support inequalities,
and the existing finite-root selection and exposed-vertex arguments apply.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.LocalRootSupport
open HomogeneousSubharmonicConvex SectorScaledNeighborhood
open ZeroDensity.LocalRootSelection
set_option backward.isDefEq.respectTransparency false

def unitPoint (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem rotation_unitPoint (m θ : ℝ) : rotation m (unitPoint θ) = unitPoint (m + θ) := by
  simp only [HomogeneousSubharmonicConvex.rotation, unitPoint,
    Complex.ofReal_add, add_mul, Complex.exp_add]

theorem cos_smul_tangentPoint {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Real.cos θ • tangentPoint (Real.tan θ) = unitPoint θ := by
  apply Complex.ext
  · simp only [Complex.smul_re, tangentPoint_re, smul_eq_mul, mul_one,
      unitPoint, Complex.exp_ofReal_mul_I_re]
  · simp only [Complex.smul_im, tangentPoint_im, smul_eq_mul, unitPoint,
      Complex.exp_ofReal_mul_I_im, Real.tan_eq_sin_div_cos]
    field_simp

theorem tangentPoint_polar (t : ℝ) :
    tangentPoint t = (Real.cos (Real.arctan t))⁻¹ • unitPoint (Real.arctan t) := by
  have h := cos_smul_tangentPoint (Real.cos_arctan_pos t).ne'
  rw [Real.tan_arctan] at h
  rw [← h, smul_smul, inv_mul_cancel₀ (Real.cos_arctan_pos t).ne', one_smul]

theorem rotation_smul (m r : ℝ) (z : ℂ) : rotation m (r • z) = r • rotation m z := by
  simp only [HomogeneousSubharmonicConvex.rotation, mul_smul_comm]

theorem rotated_tangent_polar (m t : ℝ) :
    rotation m (tangentPoint t) =
      (Real.cos (Real.arctan t))⁻¹ • unitPoint (m + Real.arctan t) := by
  rw [tangentPoint_polar, rotation_smul, rotation_unitPoint]

theorem positive_unitPoint_mem_fullCone {J : Set ℝ} {θ r : ℝ}
    (hθ : θ ∈ J) (hr : 0 < r) : r • unitPoint θ ∈ fullCone J := by
  refine ⟨(Real.log r : ℂ) + (θ : ℂ) * Complex.I, ?_, ?_⟩
  · simpa using hθ
  · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    rfl

theorem centered_angle_bounds {l u m : ℝ} (hm : m = (l + u) / 2)
    (hshort : u - l < Real.pi) {θ : ℝ} (hθ : θ ∈ Icc l u) :
    θ - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [hm]
  constructor <;> linarith [hθ.1, hθ.2]

theorem angle_of_tangent_mem {l u m : ℝ}
    (hl : l - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hu : u - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Ioo (Real.tan (l - m)) (Real.tan (u - m))) :
    m + Real.arctan t ∈ Ioo l u := by
  have ha := Real.arctan_strictMono ht.1
  have hb := Real.arctan_strictMono ht.2
  rw [Real.arctan_tan hl.1 hl.2] at ha
  rw [Real.arctan_tan hu.1 hu.2] at hb
  constructor <;> linarith

theorem tangent_of_angle_mem {l u m θ : ℝ}
    (hl : l - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hu : u - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hθ : θ ∈ Ioo l u) :
    Real.tan (θ - m) ∈ Ioo (Real.tan (l - m)) (Real.tan (u - m)) := by
  have hθb : θ - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hl.1, hu.2, hθ.1, hθ.2]
  exact ⟨Real.strictMonoOn_tan hl hθb (by linarith [hθ.1]),
    Real.strictMonoOn_tan hθb hu (by linarith [hθ.2])⟩

theorem rotated_tangent_projection (μ : ℂ) (m t : ℝ) :
    (μ * rotation m (tangentPoint t)).re =
      -(μ * unitPoint m).im * t + (μ * unitPoint m).re := by
  change (μ * (unitPoint m * tangentPoint t)).re = _
  rw [← mul_assoc, Complex.mul_re, tangentPoint_re, tangentPoint_im]
  ring

theorem rotated_tangent_projection_polar (μ : ℂ) (m t : ℝ) :
    (μ * rotation m (tangentPoint t)).re =
      (Real.cos (Real.arctan t))⁻¹ * projection μ (m + Real.arctan t) := by
  rw [rotated_tangent_polar, mul_smul_comm, Complex.smul_re, projection_eq]
  rfl

/-- Every root selected on an open angular interval is a genuine global
minorant. The support inequality is proved from subharmonicity and positive
homogeneity, rather than assumed. -/
theorem selected_projection_le (roots : Finset ℂ) {H : ℂ → ℝ} {h : ℝ → ℝ}
    {l u : ℝ} (hlu : l < u) (hshort : u - l < Real.pi)
    (hH : SubharmonicOn H (fullCone (Ioo l u)))
    (hpolar : ∀ θ ∈ Ioo l u, ∀ r : ℝ, 0 < r →
      H (r • unitPoint θ) = r * h θ) :
    ∀ μ ∈ selected roots h l u, ∀ θ ∈ Ioo l u, projection μ θ ≤ h θ := by
  classical
  let m : ℝ := (l + u) / 2
  have hl : l - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    centered_angle_bounds rfl hshort ⟨le_rfl, hlu.le⟩
  have hu : u - m ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    centered_angle_bounds rfl hshort ⟨hlu.le, le_rfl⟩
  let S : Set ℝ := Ioo (Real.tan (l - m)) (Real.tan (u - m))
  let F : ℂ → ℝ := fun z => H (rotation m z)
  let g : ℝ → ℝ := fun t => F (tangentPoint t)
  have hangle : ∀ t ∈ S, m + Real.arctan t ∈ Ioo l u :=
    fun _ ht => angle_of_tangent_mem hl hu ht
  have hgp : ∀ t ∈ S, g t =
      (Real.cos (Real.arctan t))⁻¹ * h (m + Real.arctan t) := by
    intro t ht
    dsimp [g, F]
    rw [rotated_tangent_polar]
    exact hpolar _ (hangle t ht) _ (inv_pos.mpr (Real.cos_arctan_pos t))
  have hmap : tangentCone S ⊆ rotation m ⁻¹' fullCone (Ioo l u) := by
    intro z hz
    change rotation m z ∈ fullCone (Ioo l u)
    rw [← tangent_decomposition (ne_of_gt hz.1), rotation_smul, rotated_tangent_polar,
      smul_smul]
    exact positive_unitPoint_mem_fullCone (hangle _ hz.2)
      (mul_pos hz.1 (inv_pos.mpr (Real.cos_arctan_pos _)))
  have hF : SubharmonicOn F (tangentCone S) := (subharmonicOn_rotation hH m).mono hmap
  have hhom : ∀ r : ℝ, 0 < r → ∀ t ∈ S,
      F (r • tangentPoint t) = r * F (tangentPoint t) := by
    intro r hr t ht
    change H (rotation m (r • tangentPoint t)) = r * H (rotation m (tangentPoint t))
    rw [rotation_smul, rotated_tangent_polar, smul_smul]
    rw [hpolar _ (hangle t ht) _
      (mul_pos hr (inv_pos.mpr (Real.cos_arctan_pos t))),
      hpolar _ (hangle t ht) _ (inv_pos.mpr (Real.cos_arctan_pos t))]
    ring
  have hconv : ConvexOn ℝ S g := tangent_convexOn (convex_Ioo _ _) hF hhom
  intro μ hμ θ hθ
  obtain ⟨_, a, b, hab, hsub, heq⟩ := Finset.mem_filter.mp hμ
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hcJ := hsub hc
  let t₀ : ℝ := Real.tan (c - m)
  have ht₀ : t₀ ∈ S := tangent_of_angle_mem hl hu hcJ
  have hct : m + Real.arctan t₀ = c := by
    have hcb := centered_angle_bounds (l := l) (u := u) (m := m) rfl hshort
      (Ioo_subset_Icc_self hcJ)
    rw [Real.arctan_tan hcb.1 hcb.2]
    ring
  have hn : S ∩ (fun t : ℝ => m + Real.arctan t) ⁻¹' Ioo a b ∈ 𝓝 t₀ := by
    apply (isOpen_Ioo.inter (isOpen_Ioo.preimage
      (continuous_const.add Real.continuous_arctan))).mem_nhds
    refine ⟨ht₀, ?_⟩
    change m + Real.arctan t₀ ∈ Ioo a b
    rwa [hct]
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hn
  have hlocal : ZeroDensity.ConvexSelection.locallySelected g S
      (-(μ * unitPoint m).im) (μ * unitPoint m).re := by
    refine ⟨t₀ - δ / 2, t₀ + δ / 2, by linarith, ?_, ?_⟩
    · intro t ht
      exact (hd (by rw [mem_ball, Real.dist_eq, abs_lt]
                    constructor <;> linarith [ht.1, ht.2])).1
    · intro t ht
      have htd := hd (show t ∈ ball t₀ δ by
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2])
      rw [hgp t htd.1, heq _ htd.2, ← rotated_tangent_projection_polar,
        rotated_tangent_projection]
  have ht : Real.tan (θ - m) ∈ S := tangent_of_angle_mem hl hu hθ
  have hminor := ZeroDensity.ConvexSelection.locallySelected_minorant hconv hlocal _ ht
  rw [← rotated_tangent_projection, rotated_tangent_projection_polar, hgp _ ht] at hminor
  have hθb := centered_angle_bounds (l := l) (u := u) (m := m) rfl hshort
    (Ioo_subset_Icc_self hθ)
  have hθeq : m + Real.arctan (Real.tan (θ - m)) = θ := by
    rw [Real.arctan_tan hθb.1 hθb.2]
    ring
  rw [hθeq] at hminor
  exact le_of_mul_le_mul_left hminor (inv_pos.mpr (Real.cos_arctan_pos _))

/-- The complete finite maximum and vertex assertions of Lemma 3.3, given
the continuous subharmonic homogeneous finite-root indicator of Lemma 3.2. -/
theorem local_root_selection (roots : Finset ℂ) {H : ℂ → ℝ} {h : ℝ → ℝ}
    {l u : ℝ} (hlu : l < u) (hshort : u - l < Real.pi)
    (hH : SubharmonicOn H (fullCone (Ioo l u)))
    (hpolar : ∀ θ ∈ Ioo l u, ∀ r : ℝ, 0 < r →
      H (r • unitPoint θ) = r * h θ)
    (hh : ContinuousOn h (Ioo l u))
    (halt : ∀ θ ∈ Ioo l u, ∃ μ ∈ roots, h θ = projection μ θ) :
    ∃ hne : (selected roots h l u).Nonempty,
      (∀ θ ∈ Ioo l u, h θ = (selected roots h l u).sup' hne (fun μ => projection μ θ)) ∧
      (convexHull ℝ (((selected roots h l u).image star : Finset ℂ) : Set ℂ)).extremePoints ℝ =
        (((selected roots h l u).image star : Finset ℂ) : Set ℂ) := by
  classical
  have hminor := selected_projection_le roots hlu hshort hH hpolar
  refine ⟨selected_nonempty roots hlu hh halt, ?_,
    V10.SelectedVertices.conjugate_selected_are_exact_vertices roots h l u hminor⟩
  intro θ hθ
  apply le_antisymm
  · obtain ⟨μ, hμ, he⟩ := selected_covers roots hh halt hθ
    rw [he]
    exact Finset.le_sup' (fun μ => projection μ θ) hμ
  · apply Finset.sup'_le
    intro μ hμ
    exact hminor μ hμ θ hθ

#print axioms selected_projection_le
#print axioms local_root_selection

end V10.LocalRootSupport
