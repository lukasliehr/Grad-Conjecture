import CQ2CompletedProjection
import QP9Consumer

noncomputable section

namespace Grad.RealFixedRanges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisCore
open Grad.SmoothingFamily Grad.Cor18 Grad.QuotientProjection

/-- The unique actual COR19 extension, not a supplied abstract projection. -/
def stateProjection (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    XAmbient parameters grade →L[ℂ] XAmbient parameters grade :=
  Classical.choose (actualCompletedProjection parameters parameter inside grade large)

theorem stateProjection_core (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateCore parameters) :
    stateProjection parameters parameter inside grade large (stateToGrade parameters grade field) =
      stateToGrade parameters grade (fullProjection parameters parameter inside field) :=
  (Classical.choose_spec (Classical.choose_spec
    (actualCompletedProjection parameters parameter inside grade large))).2.2.1 field

theorem stateProjection_idempotent (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ∀ field, stateProjection parameters parameter inside grade large
      (stateProjection parameters parameter inside grade large field) =
        stateProjection parameters parameter inside grade large field :=
  (Classical.choose_spec (Classical.choose_spec
    (actualCompletedProjection parameters parameter inside grade large))).2.2.2.2.1

/-- The unique actual extension supplied by the accepted COR21 consumer. -/
def sourceProjection (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade :=
  Classical.choose (Classical.choose_spec (completedQuotientProjection_exists parameters grade large)).2

theorem sourceProjection_core (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : SmoothQuotient parameters) :
    sourceProjection parameters grade large (quotientEta parameters grade field) =
      quotientEta parameters grade (quotientProjection parameters field) :=
  (Classical.choose_spec
    (Classical.choose_spec (completedQuotientProjection_exists parameters grade large)).2).1 field

theorem sourceProjection_idempotent (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∀ field, sourceProjection parameters grade large (sourceProjection parameters grade large field) =
      sourceProjection parameters grade large field :=
  (Classical.choose_spec
    (Classical.choose_spec (completedQuotientProjection_exists parameters grade large)).2).2.2.1

end Grad.RealFixedRanges
