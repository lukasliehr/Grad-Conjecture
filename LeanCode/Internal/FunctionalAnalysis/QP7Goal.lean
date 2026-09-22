import QP1LiteralMaps

noncomputable section

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.AxisCore

/-- COR21: the displayed maps, literal fourfold Hilbert norm, all grades q ≥ 3,
and the four simultaneous kernels. No unspecified projection is assumed. -/
def SmoothQuotientProjectionGoal : Prop :=
  ∀ parameters : PhaseParameters,
    (∀ family, affineTrace parameters (affineInsertion parameters family) = family) ∧
    (∀ family, modeProjection parameters (affineInsertion parameters family) = 0) ∧
    (∀ field, affineTrace parameters (modeProjection parameters field) = 0) ∧
    (∀ grade : ℕ, 3 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ field : SmoothQuotient parameters,
        quotientNorm parameters grade (quotientProjection parameters field) ≤
          constant * quotientNorm parameters grade field) ∧
    (∀ field, quotientProjection parameters (quotientProjection parameters field) =
      quotientProjection parameters field) ∧
    (∀ field : SmoothQuotient parameters,
      (∃ source, quotientProjection parameters source = field) ↔
        angularCore parameters 0 (field 3) = 0 ∧
        angularCore parameters 0 (field 2) = 0 ∧
        modeProjection parameters field = 0 ∧ affineTrace parameters field = 0)

end Grad.QuotientProjection
