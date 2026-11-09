import Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-! Local continuous subharmonicity assembles on the full open domain. -/

noncomputable section
open Set
namespace V10.SubharmonicLocal

theorem subharmonicOn_of_local {f : ℂ → ℝ} {S : Set ℂ}
    (hlocal : ∀ x ∈ S, ∃ D : Set ℂ, IsOpen D ∧ x ∈ D ∧ SubharmonicOn f D) :
    SubharmonicOn f S := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨D, hD, hxD, hf⟩ := hlocal x hx
    exact (hf.cont.continuousAt (hD.mem_nhds hxD)).continuousWithinAt
  · intro x hx
    obtain ⟨D, hD, hxD, hf⟩ := hlocal x (interior_subset hx)
    exact hf.submean' x (by simpa only [hD.interior_eq] using hxD)

#print axioms subharmonicOn_of_local
end V10.SubharmonicLocal
