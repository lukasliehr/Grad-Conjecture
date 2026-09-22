import Q24MixedMap
import Q24GradeCompatibility

noncomputable section

open scoped ContDiff

namespace Grad.Q24Realization

/-- Equality of actual nonlinear maps on an open domain implies equality
of every actual derivative under bounded input/output grade maps. -/
theorem derivative_compatibility_on_open {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (input : E →L[ℝ] E') (output : F →L[ℝ] F')
    (first : E → F) (second : E' → F') (domain : Set E) (targetDomain : Set E')
    (openDomain : IsOpen domain) (openTarget : IsOpen targetDomain)
    (maps : Set.MapsTo input domain targetDomain)
    (firstSmooth : ContDiffOn ℝ ∞ first domain) (secondSmooth : ContDiffOn ℝ ∞ second targetDomain)
    (agreement : ∀ point ∈ domain, output (first point) = second (input point))
    (order : ℕ) (base : E) (inside : base ∈ domain) (directions : Fin order → E) :
    output (iteratedFDeriv ℝ order first base directions) =
      iteratedFDeriv ℝ order second (input base) (fun position => input (directions position)) := by
  have same : Set.EqOn (output ∘ first) (second ∘ input) domain := agreement
  have identity := iteratedFDerivWithin_congr (𝕜 := ℝ) same inside order
  rw [iteratedFDerivWithin_of_isOpen order openDomain inside,
    iteratedFDerivWithin_of_isOpen order openDomain inside] at identity
  have post := output.iteratedFDeriv_comp_left
    (firstSmooth.contDiffAt (openDomain.mem_nhds inside))
    (i := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [post] at identity
  exact (congrArg (fun derivative => derivative directions) identity).trans
    (iteratedFDeriv_precomp_on_open input second targetDomain openTarget secondSmooth order base
      (maps inside) directions)

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.ConstrainedGrades

theorem completedMixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (state : MixedAmbient parameters (upper + 6))
    (inside : state ∈ mixedDomain parameters (upper + 6)) :
    zLowering parameters ordered (completedMixedSlice parameters cellLength reference upper state) =
      completedMixedSlice parameters cellLength reference lower
        (mixedLowering parameters (Nat.add_le_add_right ordered 6) state) := by
  rw [completedMixedSlice_agrees parameters cellLength reference insideR upper state inside.1,
    completedMixedSlice_agrees parameters cellLength reference insideR lower
      (mixedLowering parameters (Nat.add_le_add_right ordered 6) state) inside.1]
  exact completedFixedSlice_gradeCompatibility parameters cellLength reference insideR _ inside.1 ordered
    (mixedJoint parameters (upper + 6) state) inside.2

theorem completedMixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (order : ℕ) (state : MixedAmbient parameters (upper + 6))
    (inside : state ∈ mixedDomain parameters (upper + 6))
    (directions : Fin order → MixedAmbient parameters (upper + 6)) :
    zLowering parameters ordered
      (iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference upper) state directions) =
    iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference lower)
      (mixedLowering parameters (Nat.add_le_add_right ordered 6) state)
      (fun position => mixedLowering parameters (Nat.add_le_add_right ordered 6) (directions position)) := by
  exact derivative_compatibility_on_open
    (mixedLowering parameters (Nat.add_le_add_right ordered 6)) ((zLowering parameters ordered).restrictScalars ℝ)
    (completedMixedSlice parameters cellLength reference upper) (completedMixedSlice parameters cellLength reference lower)
    (mixedDomain parameters (upper + 6)) (mixedDomain parameters (lower + 6))
    (mixedDomain_isOpen parameters (upper + 6)) (mixedDomain_isOpen parameters (lower + 6))
    (fun value member => (mixedLowering_domain_iff parameters (Nat.add_le_add_right ordered 6) value).2 member)
    (completedMixedSlice_contDiffOn parameters cellLength reference upper)
    (completedMixedSlice_contDiffOn parameters cellLength reference lower)
    (completedMixedSlice_gradeCompatibility parameters cellLength reference insideR ordered) order state inside directions

end Grad.Q24Realization
