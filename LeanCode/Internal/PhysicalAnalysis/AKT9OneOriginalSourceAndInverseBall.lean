import AKN38ExactOriginalSourceRestrictionFamily
import AKP10ActualCompatibleAllGradeSolutionFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.ActualPuncturedFamily
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.AnnularCoupledInverse Grad.AnnularStrongData Grad.AnnularStrongOrbit
open Grad.AnnularExhaustionEstimate Grad.AnnularHighGenerators Grad.AnnularCrossOrbit
open Grad.ExhaustionSourceAllocation Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Allocation

/-- One positive primitive ball supplies both existing constructions.
It is fixed before the source, the collar and every higher running grade. -/
def originalExhaustionPrimitiveRadius (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  min (coupledPrimitiveRadius parameters length compact) (originalCoefficientLowRadius parameters length)

theorem originalExhaustionPrimitiveRadius_positive (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) : 0 < originalExhaustionPrimitiveRadius parameters length compact :=
  lt_min (coupledPrimitiveRadius_positive parameters length compact lengthPositive)
    (originalCoefficientLowRadius_positive parameters length)

theorem originalExhaustionPrimitiveRadius_inverse (parameters : PhaseParameters) (length compact rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 8 ≤ originalExhaustionPrimitiveRadius parameters length compact) :
    physicalBudget parameters field rho epsilon 8 ≤ coupledPrimitiveRadius parameters length compact :=
  small.trans (min_le_left _ _)

theorem originalExhaustionPrimitiveRadius_source (parameters : PhaseParameters) (length compact rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 8 ≤ originalExhaustionPrimitiveRadius parameters length compact) :
    physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length :=
  (physicalBudget_monotone parameters field rho epsilon (by norm_num : 6 ≤ 8)).trans
    (small.trans (min_le_right _ _))

/-- The literal actual source allocated at the existing inverse context. -/
def actualExhaustionContextDatum (parameters : PhaseParameters) (length compact : ℝ)
    (context : CoupledCoordinateContext parameters length compact)
    (sourceSmall : physicalBudget parameters context.state.val.val.field context.state.val.val.rho
      context.state.val.val.epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (source : Grad.QuotientProjection.SmoothQuotient parameters) (flat : Grad.FlatSourceProjection.IsFlat source)
    (grade : ℕ) : OriginalStrongCarrier parameters context.lower 0 0 :=
  actualOriginalSourceDatum parameters length context.state.val.val.rho context.state.val.val.epsilon
    context.state.val.val.field sourceSmall context.lower context.positive
    (context.lowerHalf.trans_lt (by norm_num)) grade source flat

theorem actualExhaustionContextDatum_zeroBoundary (parameters : PhaseParameters) (length compact : ℝ)
    (context : CoupledCoordinateContext parameters length compact)
    (sourceSmall : physicalBudget parameters context.state.val.val.field context.state.val.val.rho
      context.state.val.val.epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (source : Grad.QuotientProjection.SmoothQuotient parameters) (flat : Grad.FlatSourceProjection.IsFlat source)
    (grade : ℕ) :
    zeroBoundaryDatum parameters context.lower (actualExhaustionContextDatum parameters length compact context sourceSmall source flat grade) =
      actualExhaustionContextDatum parameters length compact context sourceSmall source flat grade := rfl

end Grad.ActualPuncturedFamily
