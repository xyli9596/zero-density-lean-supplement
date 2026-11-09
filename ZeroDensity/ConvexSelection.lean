import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Convex geometry for the local root-selection argument. Convexity of the
homogeneous ODE indicator in tangent coordinates is not proved in this module. -/
noncomputable section
namespace ZeroDensity.ConvexSelection
open Set

/-- Agreement on a nonempty open interval makes an affine line a global support. -/
theorem affine_minorant_of_local_agreement {g : ℝ → ℝ} {S : Set ℝ}
    (hg : ConvexOn ℝ S g) {a b A B : ℝ} (hab : a < b)
    (hsub : Ioo a b ⊆ S) (he : ∀ x ∈ Ioo a b, g x = A*x+B) :
    ∀ x ∈ S, A*x+B ≤ g x := by
  let c := (2*a+b)/3
  let d := (a+2*b)/3
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hd : d ∈ Ioo a b := by dsimp [d]; constructor <;> linarith
  have hcd : c < d := by dsimp [c,d]; linarith
  have hgc := he c hc
  have hgd := he d hd
  have hslope : (g d-g c)/(d-c) = A := by
    rw [hgc,hgd]
    apply (div_eq_iff (ne_of_gt (sub_pos.mpr hcd))).mpr
    ring
  intro x hx
  by_cases hxc : x < c
  · have hh := hg.slope_mono_adjacent hx (hsub hd) hxc hcd
    rw [hslope] at hh
    have hmul := (div_le_iff₀ (sub_pos.mpr hxc)).mp hh
    rw [hgc] at hmul
    nlinarith
  · by_cases hdx : d < x
    · have hh := hg.slope_mono_adjacent (hsub hc) hx hcd hdx
      rw [hslope] at hh
      have hmul := (le_div_iff₀ (sub_pos.mpr hdx)).mp hh
      rw [hgd] at hmul
      nlinarith
    · have hxi : x ∈ Ioo a b := by
        constructor <;> linarith [hc.1, hd.2, le_of_not_gt hxc, le_of_not_gt hdx]
      exact (he x hxi).ge

/-- An affine alternative is selected by actual agreement on a nonempty
open subinterval, rather than by an assumed global support inequality. -/
def locallySelected (g : ℝ → ℝ) (S : Set ℝ) (A B : ℝ) : Prop :=
  ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S ∧ ∀ x ∈ Ioo a b, g x = A*x+B

theorem locallySelected_minorant {g : ℝ → ℝ} {S : Set ℝ}
    (hg : ConvexOn ℝ S g) {A B : ℝ} (h : locallySelected g S A B) :
    ∀ x ∈ S, A*x+B ≤ g x := by
  obtain ⟨a,b,hab,hsub,he⟩ := h
  exact affine_minorant_of_local_agreement hg hab hsub he

/-- Finite selected lines which cover every point represent a convex function
as their pointwise maximum. No minorant hypothesis is supplied. -/
theorem selected_finite_max {ι : Type*} (lines : Finset ι) (A B : ι → ℝ)
    {g : ℝ → ℝ} {S : Set ℝ} (hg : ConvexOn ℝ S g)
    (hlocal : ∀ i ∈ lines, locallySelected g S (A i) (B i))
    (hcover : ∀ x ∈ S, ∃ i ∈ lines, g x = A i*x+B i) :
    ∀ x ∈ S, ∃ i ∈ lines, g x = A i*x+B i ∧
      ∀ j ∈ lines, A j*x+B j ≤ A i*x+B i := by
  intro x hx
  obtain ⟨i,hi,he⟩ := hcover x hx
  refine ⟨i,hi,he,?_⟩
  intro j hj
  rw [← he]
  exact locallySelected_minorant hg (hlocal j hj) x hx

/-- Pointwise equality with the actual finite maximum of the selected lines. -/
theorem selected_sup_eq {ι : Type*} (lines : Finset ι) (hne : lines.Nonempty)
    (A B : ι → ℝ) {g : ℝ → ℝ} {S : Set ℝ} (hg : ConvexOn ℝ S g)
    (hlocal : ∀ i ∈ lines, locallySelected g S (A i) (B i))
    (hcover : ∀ x ∈ S, ∃ i ∈ lines, g x = A i*x+B i) :
    ∀ x ∈ S, g x = lines.sup' hne (fun i => A i*x+B i) := by
  intro x hx
  apply le_antisymm
  · obtain ⟨i,hi,he⟩ := hcover x hx
    rw [he]
    exact Finset.le_sup' (fun i => A i*x+B i) hi
  · apply Finset.sup'_le
    intro i hi
    exact locallySelected_minorant hg (hlocal i hi) x hx

#print axioms selected_sup_eq
#print axioms affine_minorant_of_local_agreement
#print axioms locallySelected_minorant
#print axioms selected_finite_max
end ZeroDensity.ConvexSelection
