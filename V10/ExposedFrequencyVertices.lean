import V10.SelectedVertices
import Mathlib.Tactic

/-!
# Current Corollary 3.8: frequencies exposed by their own radial normal

This is the complete finite convex-geometric characterization. It does not
claim the analytic strip-count conclusion of Proposition 3.7.
-/

noncomputable section
open Set
namespace V10.ExposedFrequencyVertices
open ZeroDensity.PolygonFaces

def radialNormal (ω : ℂ) : ℂ →ₗ[ℝ] ℝ :=
  ω.re • Complex.reLm + ω.im • Complex.imLm

theorem radialNormal_apply (ω ν : ℂ) : radialNormal ω ν = (ν * star ω).re := by
  simp [radialNormal, Complex.mul_re]
  ring

theorem radialNormal_self (ω : ℂ) : radialNormal ω ω = Complex.normSq ω := by
  simp [radialNormal, Complex.normSq_apply]

theorem ratio_lt_iff {ω ν : ℂ} (hω : ω ≠ 0) :
    (ν / ω).re < 1 ↔ radialNormal ω ν < radialNormal ω ω := by
  rw [radialNormal_apply, radialNormal_self]
  simp only [Complex.div_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, mul_neg, sub_neg_eq_add]
  rw [← add_div, div_lt_iff₀ (Complex.normSq_pos.mpr hω), one_mul]

theorem strict_max_iff_face (s : Finset ℂ) {ω : ℂ} (hω : ω ∈ s)
    (L : ℂ →ₗ[ℝ] ℝ) :
    (∀ ν ∈ s, ν ≠ ω → L ν < L ω) ↔ linearFace s L = {ω} := by
  classical
  let hs : s.Nonempty := ⟨ω, hω⟩
  constructor
  · intro h
    have he : s.sup' hs L = L ω := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro ν hν
        by_cases hνω : ν = ω
        · simp [hνω]
        · exact (h ν hν hνω).le
      · exact Finset.le_sup' L hω
    have hm : maximizingPoints s hs L = {ω} := by
      ext ν
      simp only [maximizingPoints, Finset.mem_filter, Finset.mem_singleton, he]
      constructor
      · rintro ⟨hν, heq⟩
        by_contra hne
        exact (h ν hν hne).ne heq
      · rintro rfl
        exact ⟨hω, rfl⟩
    rw [linearFace_eq_convexHull s hs L, hm]
    simp
  · intro he ν hν hne
    have hw : ω ∈ linearFace s L := by rw [he]; exact mem_singleton ω
    have hνh : ν ∈ convexHull ℝ (s : Set ℂ) := subset_convexHull ℝ _ hν
    apply lt_of_le_of_ne (hw.2 ν hνh)
    intro heq
    have hνf : ν ∈ linearFace s L := ⟨hνh, fun z hz => by rw [heq]; exact hw.2 z hz⟩
    rw [he] at hνf
    exact hne hνf

def frequencyHull (F : Finset ℂ) : Set ℂ := convexHull ℝ ((insert 0 F : Finset ℂ) : Set ℂ)

def ownLine (ω : ℂ) : Set ℂ := {ν | (ν * star ω).re = Complex.normSq ω}

/-- The actual perpendicular level line supports the hull at ω alone iff
the radial frequency ratios satisfy the manuscript's strict inequalities. -/
theorem corollary_3_8 (F : Finset ℂ) (ω : ℂ) :
    (ω ∈ F ∧ ω ≠ 0 ∧ ∀ ν ∈ insert 0 F, ν ≠ ω → (ν / ω).re < 1) ↔
    (ω ≠ 0 ∧ ω ∈ (frequencyHull F).extremePoints ℝ ∧
      (∀ ν ∈ frequencyHull F, (ν * star ω).re ≤ Complex.normSq ω) ∧
      frequencyHull F ∩ ownLine ω = {ω}) := by
  classical
  constructor
  · rintro ⟨hωF, hω, hratio⟩
    have hw : ω ∈ insert 0 F := Finset.mem_insert_of_mem hωF
    have hstrict : ∀ ν ∈ insert 0 F, ν ≠ ω → radialNormal ω ν < radialNormal ω ω :=
      fun ν hν hne => ratio_lt_iff hω |>.mp (hratio ν hν hne)
    have hface := (strict_max_iff_face (insert 0 F) hw (radialNormal ω)).mp hstrict
    have hwface : ω ∈ linearFace (insert 0 F) (radialNormal ω) := by
      rw [hface]
      exact mem_singleton ω
    have hle : ∀ ν ∈ frequencyHull F, (ν * star ω).re ≤ Complex.normSq ω := by
      intro ν hν
      simpa only [radialNormal_self, radialNormal_apply] using hwface.2 ν hν
    refine ⟨hω, V10.SelectedVertices.extreme_of_strict_linear_max _ hw _ hstrict, hle, ?_⟩
    apply subset_antisymm
    · intro ν hν
      have hνf : ν ∈ linearFace (insert 0 F) (radialNormal ω) := by
        refine ⟨hν.1, ?_⟩
        intro z hz
        simp only [radialNormal_apply]
        rw [hν.2]
        exact hle z hz
      rwa [hface] at hνf
    · intro ν hν
      subst ν
      refine ⟨hwface.1, ?_⟩
      change (ω * star ω).re = Complex.normSq ω
      rw [← radialNormal_apply, radialNormal_self]
  · rintro ⟨hω, hvertex, hle, he⟩
    have hw : ω ∈ (insert 0 F : Finset ℂ) :=
      extremePoints_convexHull_subset (𝕜 := ℝ) hvertex
    have hωF : ω ∈ F := (Finset.mem_insert.mp hw).resolve_left hω
    refine ⟨hωF, hω, ?_⟩
    intro ν hν hne
    apply (ratio_lt_iff hω).mpr
    have hνh : ν ∈ frequencyHull F := subset_convexHull ℝ _ hν
    have hνle := hle ν hνh
    rw [← radialNormal_apply, ← radialNormal_self] at hνle
    apply lt_of_le_of_ne hνle
    intro htie
    have hνline : ν ∈ ownLine ω := by
      change (ν * star ω).re = Complex.normSq ω
      simpa only [radialNormal_self, radialNormal_apply] using htie
    have hνeq : ν ∈ ({ω} : Set ℂ) := he ▸ ⟨hνh, hνline⟩
    exact hne hνeq

#print axioms corollary_3_8
end V10.ExposedFrequencyVertices
