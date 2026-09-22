import AFT1OriginalScalarNecessity
import AFI6OriginalNonexceptionalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalNonexceptionalUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.CircularHighWeak Grad.ActualSmoothRobin Grad.CartesianScalarElimination
open Grad.ActualScalarForcing Grad.ActualScalarResidual Grad.ActualNonexceptionalInverse
open Grad.ActualReferenceAssembly Grad.ActualForcingSupport Grad.ActualScalarAxis Grad.RawCircularSectors Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

private theorem robin_from_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    (robin forcing boundary : E) (scalar : ℂ) (equation : robin + scalar • forcing = scalar • boundary) :
    robin = scalar • (boundary - forcing) := by
  rw [smul_sub, ← equation]
  abel

theorem lowRobin_coefficient_zero (field : ClosedJet 1) (mode : ℤ) (low : mode ∈ lowAngularModes) :
    angularClosedJet mode (robinResidualJet (excludedAngularJet lowAngularModes field)) = 0 := by
  simp only [robinResidualJet, angularClosedJet_add, angularClosedJet_smul, angularClosedJet_euler,
    excludedAngularJet_low_zero field mode low, smul_zero, add_zero]
  exact Grad.CircularNormalLift.eulerJetLinear.map_zero

/-- Every original circular solution satisfies the literal scalar high Robin
condition. This is the reverse of the actual physical boundary elimination. -/
theorem originalRows_robin_coefficient (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (source : SmoothCapSource L sigma gamma ell) (sourceExcluded : AvoidsExceptionalSource source)
    (rows : circularRows admissible state.val = source) (beta : BandSmoothBoundary L sigma gamma ell)
    (boundary : ∀ grade : ℕ, circularCoreTrace admissible grade state.val = beta.grade grade)
    (cell mode : ℤ) (grade : ℕ) :
    fourierCoeff (fun angle : CellCircle =>
      (robinResidualJet (excludedAngularJet lowAngularModes (apSmoothJet admissible 1 cell state.val.1))).value (boundaryDiskPoint angle)) mode =
      apBoundaryCoefficient L sigma gamma ell (grade + 1) ((forcedBoundary admissible source beta).grade grade) (mode, cell) := by
  have thetaExcluded := (originalCircularState_scalar_conditions admissible state excluded).1
  have reconstructed := originalRows_reconstruction admissible state excluded source rows
  have actualBoundary : circularCoreTrace admissible grade (reconstructedState admissible state.val.1 source) = beta.grade grade :=
    (congrArg (circularCoreTrace admissible grade) reconstructed).symm.trans (boundary grade)
  by_cases high : 3 ≤ |mode|
  · have image := congrArg (fun field : APBoundaryGrade L sigma gamma ell 1 (grade + 1) =>
      apBoundaryCoefficient L sigma gamma ell (grade + 1) (boundaryB L sigma gamma ell (grade + 1) field) (mode, cell)) actualBoundary
    have equation := (actualCircularTrace_B_coefficient admissible grade state.val.1 source thetaExcluded sourceExcluded (mode, cell) high).symm.trans
      (image.trans (boundaryB_coefficient (grade + 1) (beta.grade grade) (mode, cell)))
    have robin := robin_from_sum _ _ _ _ equation
    exact (boundaryCoefficient_angular mode _).trans
      ((congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0))
        (highRobin_coefficient mode high (apSmoothJet admissible 1 cell state.val.1))).trans
          (robin.trans (forcedBoundary_coefficient admissible source beta grade (mode, cell)).symm))
  · have low := not_highMode_low mode high
    have left : fourierCoeff (fun angle : CellCircle =>
        (robinResidualJet (excludedAngularJet lowAngularModes (apSmoothJet admissible 1 cell state.val.1))).value (boundaryDiskPoint angle)) mode = 0 :=
      (boundaryCoefficient_angular mode _).trans (congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0))
        (lowRobin_coefficient_zero _ mode low))
    have right := forcedBoundary_coefficient admissible source beta grade (mode, cell)
    rw [highMultiplier, if_pos low] at right
    simp only [Complex.ofReal_zero, zero_smul] at right
    exact left.trans right.symm

end Grad.OriginalNonexceptionalUniqueness
