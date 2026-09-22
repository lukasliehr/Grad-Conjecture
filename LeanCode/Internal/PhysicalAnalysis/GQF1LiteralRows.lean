import GQE17FaithfulPsi

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.GaugeTransfer

variable {L sigma gamma ell : ℝ}

def apSmoothPlanar (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  apSmoothValueMap L sigma gamma ell planarPartMap

def apSmoothScalar (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  apSmoothValueMap L sigma gamma ell toroidalPartMap

def apSmoothQuarter (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  apSmoothValueMap L sigma gamma ell quarterValueMap

def apSmoothTangential (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apSmoothPlanar L sigma gamma ell).comp
    ((apSmoothComplement L sigma gamma ell).comp (apSmoothValueMap L sigma gamma ell planarInclusionMap))

/-- The literal radial vector projector is I+JTJ, since -JTJ is the
radial-equivariant part. Its correspondence with N's (I+S)A/2 is a required
proof below, not an assumed projection law. -/
def apSmoothQrad (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  LinearMap.id + (apSmoothQuarter L sigma gamma ell).comp
    ((apSmoothTangential L sigma gamma ell).comp (apSmoothQuarter L sigma gamma ell))

/-- Actual scaled divergence: two planar derivatives and (ell/L)partial_zeta
of the third stored covariant coordinate. -/
def apSmoothDiv (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 0)).comp
      (apSmoothPartial admissible 3 0) +
    (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 1)).comp
      (apSmoothPartial admissible 3 1) +
    (apSmoothScalar L sigma gamma ell).comp (apSmoothAxial L sigma gamma ell 3)

def circularForceInner (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (-2 : ℂ) • ((apSmoothQuarter L sigma gamma ell).comp
      ((apSmoothGradient admissible).comp (LinearMap.fst ℂ _ _))) -
    ((apSmoothRotation admissible 2) + apSmoothQuarter L sigma gamma ell).comp
      ((apSmoothPlanar L sigma gamma ell).comp (LinearMap.snd ℂ _ _))

def circularForce (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apSmoothQrad L sigma gamma ell).comp (circularForceInner admissible)

def circularDeterminant (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  -((apSmoothRemoveMean L sigma gamma ell 1).comp
    ((apSmoothDiv admissible).comp (compensatedReconstruct admissible)))

def circularThird (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRotation admissible 1).comp
    ((apSmoothScalar L sigma gamma ell).comp (LinearMap.snd ℂ _ _))

def actualForce (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apSmoothQrad L sigma gamma ell).comp
    (circularForceInner admissible + (2 : ℂ) •
      ((apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
        (compensatedReconstruct admissible)))

def actualDeterminant (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRemoveMean L sigma gamma ell 1).comp ((apSmoothDiv admissible).comp
    ((-LinearMap.id + apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1).comp
      (compensatedReconstruct admissible)))

def actualThird (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  circularThird admissible - (2 : ℂ) •
    ((apSmoothRemoveMean L sigma gamma ell 1).comp
      ((apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2).comp
        (compensatedReconstruct admissible)))

end Grad.GaugeCoefficients.Physical.Compensated
