import ANT5ActualAngularElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Radial
open Grad.NonlinearRange Grad.NonlinearDivision Grad.ActualAngularInverse Grad.BoundaryTrace

/-- Exact homogeneous AN14 identities on the literal accepted divergence and
radial product carriers. The multiplier is the actual ANS expression I+4R^{-2},
hence the defining expression of ANB fullBJet, including the center modes ±1.
Only the zero mean of Theta and the genuine vector equation are required. -/
theorem actualHomogeneousScalarElimination (theta : ClosedJet 1) (vector : ClosedJet 2)
    (mean : angularClosedJet 0 theta = 0)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta)) :
    (planarDivJet (valueMapJet planarInclusionMap vector) + (4 : ℂ) •
      shiftInverseJet 0 (shiftInverseJet 0 (planarDivJet (valueMapJet planarInclusionMap vector))) =
        laplacianJet theta) ∧
    (apProductJet radialRowJet (valueMapJet planarInclusionMap vector) + (4 : ℂ) •
      shiftInverseJet 0 (shiftInverseJet 0 (apProductJet radialRowJet (valueMapJet planarInclusionMap vector))) =
        eulerJet theta + (2 : ℂ) • theta) := by
  constructor
  · simpa only [vectorDivJet_actual] using homogeneous_div_angularInverse theta vector mean equation
  · simpa only [vectorRadialJet_actual] using homogeneous_radial_angularInverse theta vector mean equation

/-- The literal normal scalar relation at every actual unit-circle point.
Euler differentiation is precisely the outward normal derivative there. -/
theorem actualHomogeneousBoundaryElimination (theta : ClosedJet 1) (vector : ClosedJet 2)
    (mean : angularClosedJet 0 theta = 0)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta))
    (angle : CellCircle) :
    (apProductJet radialRowJet (valueMapJet planarInclusionMap vector) + (4 : ℂ) •
      shiftInverseJet 0 (shiftInverseJet 0 (apProductJet radialRowJet (valueMapJet planarInclusionMap vector)))).value
        (boundaryDiskPoint angle) =
      fderiv ℝ (smoothClosedExtension theta) (boundaryDiskPoint angle).val (boundaryDiskPoint angle).val +
        (2 : ℂ) • theta.value (boundaryDiskPoint angle) := by
  have radial := congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint angle))
    (actualHomogeneousScalarElimination theta vector mean equation).2
  simpa only [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul,
    ContinuousMap.smul_apply, eulerJet_extension_value] using radial

end Grad.CartesianScalarElimination
