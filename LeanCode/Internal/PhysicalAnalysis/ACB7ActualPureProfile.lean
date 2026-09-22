import ACB6ActualCenterH1Bound
import ANR15RadialModes
import ANR17PolarLaplacian
import ARS2LiteralRadialSource
import AOD2ReciprocalBounds
import ARC10FiniteCartesianConsumer

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.PhysicalFamily Grad.CollarCartesian Grad.SourceBoundaryTrace

def pureExtension (mode : ℤ) (field : ClosedJet 1) : SpatialPlane → ComplexEuclidean 1 :=
  angularProjectionValue mode (smoothClosedExtension field)

theorem pureExtension_smooth (mode : ℤ) (field : ClosedJet 1) : ContDiff ℝ ∞ (pureExtension mode field) :=
  angularProjectionValue_smooth mode (smoothClosedExtension_smooth field)

theorem pureExtension_jet (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field) :
    globalClosedJet (pureExtension mode field) (pureExtension_smooth mode field) = field := pure

def pureProfile (mode : ℤ) (field : ClosedJet 1) (radius : ℝ) : ComplexEuclidean 1 :=
  pureExtension mode field (polarPlane (radius, 0))

theorem pureProfile_smooth (mode : ℤ) (field : ClosedJet 1) : ContDiff ℝ ∞ (pureProfile mode field) :=
  (pureExtension_smooth mode field).comp (polarPlane_smooth.comp (contDiff_id.prodMk contDiff_const))

theorem polarPlane_rotation_axis (radius angle : ℝ) :
    planeRotationAction angle (polarPlane (radius, 0)) = polarPlane (radius, angle) := by
  rw [physicalRotation_eq_orthogonal]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [Grad.GaugeCoefficients.Radial.planeRotationEquiv_apply,
      Grad.GaugeCoefficients.Radial.planeRotation, polarPlane, collarPlane, mul_comm]

theorem pureExtension_polar (mode : ℤ) (field : ClosedJet 1) (radius angle : ℝ) :
    pureExtension mode field (polarPlane (radius, angle)) =
      cellExponential mode angle • pureProfile mode field radius := by
  rw [← polarPlane_rotation_axis]
  change angularProjectionValue mode (smoothClosedExtension field)
    (planeRotationAction angle (polarPlane (radius, 0))) = _
  rw [angularProjectionValue_rotation, angularCharacter_neg_angle,
    Grad.AngularSobolevTruncation.angularCharacter_fourier, neg_neg]
  rw [show fourier mode (angle : CellCircle) = cellExponential mode angle from cellCharacter_coe mode angle]
  rfl

theorem pureProfile_radialCurve (mode : ℤ) (field : ClosedJet 1) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    pureProfile mode field radius = diskCoreRadialCurve mode field radius := by
  have same := radialCoefficient_projection_value field mode radius nonnegative bounded
  exact same.symm

/-- The globally smooth representative used for collar calculations is an
actual angular projection, and has exactly the original disk coefficient. -/
theorem pureProfile_within_derivative (mode : ℤ) (field : ClosedJet 1) (order : ℕ)
    (lower : ℝ) (nonnegative : 0 ≤ lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    iteratedDerivWithin order (pureProfile mode field) (Icc lower 1) radius =
      iteratedDerivWithin order (diskCoreRadialCurve mode field) (Icc lower 1) radius :=
  iteratedDerivWithin_congr (fun point member =>
    pureProfile_radialCurve mode field point (nonnegative.trans member.1) member.2) inside

end Grad.ActualCenterBounds
