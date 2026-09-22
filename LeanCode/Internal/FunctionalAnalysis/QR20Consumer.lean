import QR19Proof
import QS1CanonicalProjections

noncomputable section

namespace Grad.CompletedReality

open Grad.CartesianState Grad.Constraints Grad.SmoothingFamily Grad.AxisCore
open Grad.RealFixedRanges

/-- The COR24 consumer uses the already accepted canonical state projection,
not a newly postulated or independently supplied completed operator. -/
theorem canonicalStateProjection_conjugate (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (point : XAmbient parameters grade) :
    xConjugation parameters grade (stateProjection parameters parameter inside grade large point) =
      stateProjection parameters parameter inside grade large (xConjugation parameters grade point) := by
  obtain ⟨completed, _, _, _, _, _, commutes, unique⟩ :=
    actualCompletedReality.2.2.1 parameters parameter inside grade large
  have agrees := unique (stateProjection parameters parameter inside grade large)
    (stateProjection_core parameters parameter inside grade large)
  rw [agrees]
  exact commutes point

theorem canonicalSourceProjection_conjugate (parameters : PhaseParameters)
    (grade : ℕ) (large : 3 ≤ grade) (point : ZAmbient parameters grade) :
    zConjugation parameters grade (sourceProjection parameters grade large point) =
      sourceProjection parameters grade large (zConjugation parameters grade point) := by
  obtain ⟨_, _, completed, _, _, _, commutes, unique⟩ :=
    actualCompletedReality.2.2.2 parameters grade large
  have agrees := unique (sourceProjection parameters grade large)
    (sourceProjection_core parameters grade large)
  rw [agrees]
  exact commutes point

/-- Actual projected real points remain real, the prerequisite needed for
the state-side projected-core density construction. -/
theorem canonicalStateProjection_preserves_real (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (point : XAmbient parameters grade)
    (realPoint : xConjugation parameters grade point = point) :
    xConjugation parameters grade (stateProjection parameters parameter inside grade large point) =
      stateProjection parameters parameter inside grade large point := by
  rw [canonicalStateProjection_conjugate, realPoint]

end Grad.CompletedReality
