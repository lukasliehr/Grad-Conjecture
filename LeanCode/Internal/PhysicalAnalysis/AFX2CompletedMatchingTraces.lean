import AFX1ActualFluxBulk

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

def smoothMatchingPrimitive (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  let flux := -LinearMap.id + apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1
  (apSmoothRemoveMean L sigma gamma ell 1).comp
    (((apSmoothRadial admissible).comp flux).comp (compensatedReconstruct admissible) +
      (((apSmoothTangent admissible).comp flux).comp
        (apSmoothFixedJet admissible matchingRadialColumnJet)).comp (physicalPsi admissible))

def completedMatchingPrimitive (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  (apMeanFree L sigma gamma ell 1 (grade + 1)).comp
    (((apRadialContraction admissible (grade + 1)).comp (apMatchingFlux admissible data (grade + 1))).comp
      (completedReconstruct admissible grade core) +
    (((apTangentContraction admissible (grade + 1)).comp (apMatchingFlux admissible data (grade + 1))).comp
      (apMatchingRadialColumn admissible (grade + 1))).comp (completedPsi admissible grade core))

theorem completedMatchingPrimitive_apply (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    completedMatchingPrimitive admissible data grade core field =
      apMatchingPrimitive admissible data (grade + 1)
        (completedReconstruct admissible grade core field) (completedPsi admissible grade core field) := rfl

theorem completedMatchingPrimitive_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) :
    completedMatchingPrimitive admissible data grade core (compensatedIntoClosure admissible grade core field) =
      apSmoothGrade L sigma gamma ell 1 (grade + 1) (smoothMatchingPrimitive admissible data coherent field.val) := by
  exact congrArg₂ (apMatchingPrimitive admissible data (grade + 1))
    (completedReconstruct_core admissible grade core field) (completedPsi_core admissible grade core field)

/-- The original AR8 primitive trace, in AP3 order `s+1/2`. -/
def completedMatchingP (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)).comp
    (completedMatchingPrimitive admissible data grade core)

/-- The retained physical scalar is `ell * R Θ`, with the original sign. -/
def completedMatchingD (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (ell : ℂ) • ((apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)).comp
    (completedPsi admissible grade core))

def completedCircleMatchingP (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  -((apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)).comp
    ((apMeanFree L sigma gamma ell 1 (grade + 1)).comp (completedRadial admissible grade core)))

theorem completedMatchingP_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) :
    completedMatchingP admissible data grade core (compensatedIntoClosure admissible grade core field) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (apSmoothGrade L sigma gamma ell 1 (grade + 1) (smoothMatchingPrimitive admissible data coherent field.val)) :=
  congrArg (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega))
    (completedMatchingPrimitive_core admissible data coherent grade core field)

theorem completedMatchingD_core (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) :
    completedMatchingD admissible grade core (compensatedIntoClosure admissible grade core field) =
      (ell : ℂ) • apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalPsi admissible field.val)) :=
  congrArg (fun psi : apGrade L sigma gamma ell 1 (grade + 1) =>
    (ell : ℂ) • apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) psi)
    (completedPsi_core admissible grade core field)

theorem completedMatchingD_transfer {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedMatchingD admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
      completedMatchingD admissible grade (circularCompensatedCore admissible) field := by
  change (ell : ℂ) • apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
    (completedPsi admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field)) =
    (ell : ℂ) • apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (completedPsi admissible grade (circularCompensatedCore admissible) field)
  exact congrArg (fun psi : apGrade L sigma gamma ell 1 (grade + 1) =>
    (ell : ℂ) • apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) psi)
    (completedPsi_transfer smooth grade large field)

theorem matchingPrimitive_transfer_difference (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade)
    (psi psiReference radialReference : apGrade L sigma gamma ell 1 grade)
    (radial : apRadialContraction admissible grade vector = radialReference) (scalar : psi = psiReference) :
    apMatchingPrimitive admissible data grade vector psi -
      -(apMeanFree L sigma gamma ell 1 grade radialReference) =
      apMeanFree L sigma gamma ell 1 grade
        (apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector) +
          apTangentContraction admissible grade
            (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psiReference))) := by
  have deviation := congrArg (fun value : apGrade L sigma gamma ell 1 grade =>
    value - -(apMeanFree L sigma gamma ell 1 grade radialReference))
      (apMatchingPrimitive_deviation admissible data grade vector psi)
  have transported := congrArg₂ (fun radialValue psiValue : apGrade L sigma gamma ell 1 grade =>
    (-apMeanFree L sigma gamma ell 1 grade radialValue +
      apMeanFree L sigma gamma ell 1 grade
        (apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector) +
          apTangentContraction admissible grade
            (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psiValue)))) -
       -(apMeanFree L sigma gamma ell 1 grade radialReference)) radial scalar
  exact deviation.trans (transported.trans (by abel))

/-- Exact AR14 on the original completed graph. Every term contains `B_C+I`;
the second term is the retained angular-radial flux correction. -/
theorem completedMatchingP_difference (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    let outputCore := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
    let output := completedTransfer smooth grade large field
    completedMatchingP admissible data grade outputCore output -
      completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (apMeanFree L sigma gamma ell 1 (grade + 1)
          (apRadialContraction admissible (grade + 1)
            (apMultiplier admissible (data.fluxDeviation (grade + 1))
              (completedReconstruct admissible grade outputCore output)) +
           apTangentContraction admissible (grade + 1)
             (apMultiplier admissible (data.fluxDeviation (grade + 1))
               (apMatchingRadialColumn admissible (grade + 1)
                 (completedPsi admissible grade (circularCompensatedCore admissible) field))))) := by
  dsimp only
  let outputCore := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
  let output := completedTransfer smooth grade large field
  let trace := apBoundaryTrace (dimension := 1) L sigma gamma ell (grade + 1) (by omega)
  have bulk := matchingPrimitive_transfer_difference admissible data (grade + 1)
    (completedReconstruct admissible grade outputCore output)
    (completedPsi admissible grade outputCore output)
    (completedPsi admissible grade (circularCompensatedCore admissible) field)
    (completedRadial admissible grade (circularCompensatedCore admissible) field)
    (completedRadial_transfer smooth grade large field) (completedPsi_transfer smooth grade large field)
  have traced := congrArg trace bulk
  simp only [map_sub, map_neg] at traced
  exact traced

end Grad.GaugeCoefficients.Physical.Compensated
