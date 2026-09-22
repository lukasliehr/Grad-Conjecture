import AJN6LiteralFullFluxSources
import AJQ4ExactSmoothSourceSystemConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularReconstruction

/-- Exact homogeneous plus once-only known input split. -/
theorem fullStrongSevenInput_split (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (field : CoupledSpace lower length positive lengthPositive) :
    fullStrongSevenInput parameters length lower lengthPositive positive bounded data field =
      homogeneousCoupledSevenInput parameters length lower lengthPositive positive field +
        knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data) := rfl

theorem fullStrongPhysicalRow_split (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (field : CoupledSpace lower length positive lengthPositive) (row : Fin 3) :
    lowPhysicalRowAction parameters length compact lower positive bounded state row
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded data field) =
    lowPhysicalRowAction parameters length compact lower positive bounded state row
      (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field) +
    lowPhysicalRowAction parameters length compact lower positive bounded state row
      (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data)) := by
  exact map_add (lowPhysicalRowAction parameters length compact lower positive bounded state row) _ _

/-- The physical storage decoder preserves addition on the actual L2 representatives. -/
theorem lowRhoPhysicalCoefficient_add_ae {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (first second : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (first + second) radius mode =
        lowRhoPhysicalCoefficient parameters lower positive first radius mode +
          lowRhoPhysicalCoefficient parameters lower positive second radius mode := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [Lp.coeFn_add (first mode) (second mode)] with radius added
  change (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
    (first mode + second mode) radius = _
  rw [added]
  simp only [Pi.add_apply, smul_add, lowRhoPhysicalCoefficient]

theorem fullStrongPhysicalCoefficient_split (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (field : CoupledSpace lower length positive lengthPositive) (row : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded state row
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded data field)) radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded state row
          (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)) radius mode +
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded state row
          (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data))) radius mode := by
  rw [fullStrongPhysicalRow_split]
  exact lowRhoPhysicalCoefficient_add_ae parameters lower positive _ _

end Grad.AnnularSmoothCore
