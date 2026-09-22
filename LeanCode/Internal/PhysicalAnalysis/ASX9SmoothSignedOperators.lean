import ASX8OriginalSmoothIntegral
import AXF22SpinMaps

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.ActualCenterVolterra Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

private theorem linear_sum_smul {E F G : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (project : F →ₗ[ℂ] G) (first second : E →ₗ[ℂ] F) (scalar : ℂ) (field : E) :
    project ((first + scalar • second) field) = project (first field) + scalar • project (second field) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]

theorem originalPartial_eq {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    Grad.GaugeCoefficients.Physical.Compensated.partialJet direction field =
      Grad.NonlinearQuotientBounds.partialJet direction field := by
  apply closedJet_eq_of_value_eq
  rfl

def smoothSignedCoordinate {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (sign : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothCoordinate admissible dimension 0 + (Complex.I * (sign : ℂ)) • apSmoothCoordinate admissible dimension 1

theorem smoothSignedCoordinate_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (sign : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (smoothSignedCoordinate admissible dimension sign field) =
      coordinateMultiplyJet (sign : ℝ) (apSmoothJet admissible dimension cell field) := by
  have value := linear_sum_smul (apSmoothJet admissible dimension cell)
    (apSmoothCoordinate admissible dimension 0) (apSmoothCoordinate admissible dimension 1) (Complex.I * (sign : ℂ)) field
  have terms := congrArg₂ (fun first second : ClosedJet dimension => first + (Complex.I * (sign : ℂ)) • second)
    (apSmoothCoordinate_jet admissible 0 field cell) (apSmoothCoordinate_jet admissible 1 field cell)
  have result := value.trans terms
  exact result.trans (by simpa only [Complex.ofReal_intCast] using (centerCoordinate_decomposition (sign : ℝ)
    (apSmoothJet admissible dimension cell field)).symm)

def smoothSignedDerivative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (sign : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothPartial admissible dimension 0 + (-(Complex.I * (sign : ℂ))) • apSmoothPartial admissible dimension 1

theorem smoothSignedDerivative_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (sign : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (smoothSignedDerivative admissible dimension sign field) =
      signedLowering sign (apSmoothJet admissible dimension cell field) := by
  have value := linear_sum_smul (apSmoothJet admissible dimension cell)
    (apSmoothPartial admissible dimension 0) (apSmoothPartial admissible dimension 1) (-(Complex.I * (sign : ℂ))) field
  have terms := congrArg₂ (fun first second : ClosedJet dimension => first + (-(Complex.I * (sign : ℂ))) • second)
    (apSmoothPartial_jet admissible field 0 cell) (apSmoothPartial_jet admissible field 1 cell)
  have bridge := congrArg₂ (fun first second : ClosedJet dimension => first + (-(Complex.I * (sign : ℂ))) • second)
    (originalPartial_eq 0 (apSmoothJet admissible dimension cell field))
    (originalPartial_eq 1 (apSmoothJet admissible dimension cell field))
  exact (value.trans (terms.trans bridge)).trans (by simp only [signedLowering, centerDifferential, neg_smul, sub_eq_add_neg])

def smoothRadiusSquare {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  (apSmoothCoordinate admissible dimension 0).comp (apSmoothCoordinate admissible dimension 0) +
    (apSmoothCoordinate admissible dimension 1).comp (apSmoothCoordinate admissible dimension 1)

theorem smoothRadiusSquare_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (smoothRadiusSquare admissible dimension field) =
      radiusPowerJet 1 (apSmoothJet admissible dimension cell field) := by
  have coordinate (direction : Fin 2) := (apSmoothCoordinate_jet admissible direction
    (apSmoothCoordinate admissible dimension direction field) cell).trans
      (congrArg (coordinateJet direction) (apSmoothCoordinate_jet admissible direction field cell))
  have value := (apSmoothJet admissible dimension cell).map_add
    (apSmoothCoordinate admissible dimension 0 (apSmoothCoordinate admissible dimension 0 field))
    (apSmoothCoordinate admissible dimension 1 (apSmoothCoordinate admissible dimension 1 field))
  exact value.trans ((congrArg₂ (fun first second : ClosedJet dimension => first + second)
    (coordinate 0) (coordinate 1)).trans (radiusPower_one_decomposition _).symm)

def smoothSignedQuotient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (sign : ℤ) (power : ℕ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  (originalPowerSmoothLinear admissible dimension power).comp (smoothSignedDerivative admissible dimension sign)

theorem smoothSignedQuotient_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (sign : ℤ) (power : ℕ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (smoothSignedQuotient admissible dimension sign power field) =
      signedQuotient sign power (apSmoothJet admissible dimension cell field) :=
  (originalPowerSmooth_jet admissible power (smoothSignedDerivative admissible dimension sign field) cell).trans
    (congrArg (powerDilationJet (power + 1)) (smoothSignedDerivative_jet admissible sign field cell))

def smoothPinnedPrimitive {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (sign : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  (smoothSignedCoordinate admissible dimension sign).comp ((smoothRadiusSquare admissible dimension).comp
    ((originalPowerSmoothLinear admissible dimension 0).comp ((smoothSignedQuotient admissible dimension sign 0).comp
      (smoothSignedQuotient admissible dimension sign 1))))

theorem smoothPinnedPrimitive_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (sign : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (smoothPinnedPrimitive admissible dimension sign field) =
      pinnedSpinPrimitive sign (apSmoothJet admissible dimension cell field) := by
  have first := smoothSignedQuotient_jet admissible sign 1 field cell
  have second := (smoothSignedQuotient_jet admissible sign 0 (smoothSignedQuotient admissible dimension sign 1 field) cell).trans
    (congrArg (signedQuotient sign 0) first)
  have integral := (originalPowerSmooth_jet admissible 0
    (smoothSignedQuotient admissible dimension sign 0 (smoothSignedQuotient admissible dimension sign 1 field)) cell).trans
      (congrArg (powerDilationJet 1) second)
  have radial := (smoothRadiusSquare_jet admissible
    (originalPowerSmooth admissible 0 (smoothSignedQuotient admissible dimension sign 0
      (smoothSignedQuotient admissible dimension sign 1 field))) cell).trans (congrArg (radiusPowerJet 1) integral)
  exact (smoothSignedCoordinate_jet admissible sign _ cell).trans
    (congrArg (coordinateMultiplyJet (sign : ℝ)) radial)

end Grad.ActualExceptionalInverse
