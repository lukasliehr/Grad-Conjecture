import AKAA12LiteralAngularKernelAction
import AKAA13LiteralPointKernel
import AKY15GivenOriginalRowConsumer

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GenericCarriers

abbrev StartupL2 (dimension : ℕ) := FieldL2 dimension openUnitDisk

def originalValueKernel {input output : ℕ} (mapping : OperatorValue input output) :
    StartupL2 input →L[ℂ] StartupL2 output :=
  startupPointKernel mapping (LinearIsometryEquiv.refl ℝ _)

/-- The actual equivariant average, with both helicity projectors. -/
def originalAverageKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  (originalValueKernel positiveHelicity).comp (startupCharacterKernel 2 1) +
    (originalValueKernel negativeHelicity).comp (startupCharacterKernel 2 (-1))

/-- The nonsingular reflection formula for the true tangential gauge T. -/
def originalTangentialKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  (1 / 2 : ℂ) • ((ContinuousLinearMap.id ℂ _ -
    startupPointKernel reflectionValueMap cartesianReflectionEquiv).comp originalAverageKernel)

/-- Literal C0=diag(T,Pi) on the full integer-cell L2 space. -/
def originalComplementKernel : StartupL2 3 →L[ℂ] StartupL2 3 :=
  (originalValueKernel planarInclusionMap).comp
    (originalTangentialKernel.comp (originalValueKernel planarPartMap)) +
  (originalValueKernel toroidalInclusionMap).comp
    ((startupCharacterKernel 1 0).comp (originalValueKernel toroidalPartMap))

def originalCircleKernel : StartupL2 3 →L[ℂ] StartupL2 3 :=
  ContinuousLinearMap.id ℂ _ - originalComplementKernel

def originalPlanarMeanFreeKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  ContinuousLinearMap.id ℂ _ - originalAverageKernel

def originalScalarMeanFreeKernel : StartupL2 1 →L[ℂ] StartupL2 1 :=
  ContinuousLinearMap.id ℂ _ - startupCharacterKernel 1 0

/-- Z1=(R-J)^{-1}(I-A), using precisely the opposite helicity shifts
 established in AKY2; no small angular modes are compressed. -/
def originalCovariantInverseKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  (startupTrueAngularInverse 2 (-1)).comp (originalValueKernel positiveHelicity) +
    (startupTrueAngularInverse 2 1).comp (originalValueKernel negativeHelicity)

def originalScalarInverseKernel : StartupL2 1 →L[ℂ] StartupL2 1 :=
  startupTrueAngularInverse 1 0

def originalGradientRecoveryKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  originalPlanarMeanFreeKernel +
    (2 : ℂ) • (originalCovariantInverseKernel.comp (originalValueKernel quarterValueMap))

def originalMatrixKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    StartupL2 input →L[ℂ] StartupL2 output :=
  startupDerivativeKernel admissible family coherent zeroDerivativeIndex

theorem originalMatrixKernel_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    ‖originalMatrixKernel admissible family coherent‖ ≤
      startupDerivativeConstant L sigma gamma zeroDerivativeIndex * ‖family 0‖ :=
  startupDerivativeKernel_norm admissible family coherent zeroDerivativeIndex

end Grad.CartesianStartup
