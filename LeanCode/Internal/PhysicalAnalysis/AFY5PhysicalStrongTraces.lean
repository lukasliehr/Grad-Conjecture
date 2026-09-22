import AFY4NativeStrongPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem completedStrongScalar_coefficient (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell (grade + 1)
      (completedStrongScalar admissible grade core field) mode =
      (Complex.I * (mode.1 : ℂ)) •
        (if 3 ≤ |mode.1| then apBoundaryCoefficient L sigma gamma ell (grade + 2)
          (completedNativeThetaTrace admissible grade core field) mode else 0) :=
  (highAngularIsometry_coefficient L sigma gamma ell (grade + 1) _ mode).trans
    (congrArg (fun value : ComplexEuclidean 1 => (Complex.I * (mode.1 : ℂ)) • value)
      (apHighProjection_coefficient L sigma gamma ell (grade + 2) _ mode))

theorem completedStrongFlux_coefficient (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell grade
      (completedStrongFlux admissible data grade core field) mode =
      (Complex.I * (mode.1 : ℂ)) •
        (if 3 ≤ |mode.1| then apBoundaryCoefficient L sigma gamma ell (grade + 1)
          (completedMatchingP admissible data grade core field) mode else 0) :=
  (highAngularIsometry_coefficient L sigma gamma ell grade _ mode).trans
    (congrArg (fun value : ComplexEuclidean 1 => (Complex.I * (mode.1 : ℂ)) • value)
      (apHighProjection_coefficient L sigma gamma ell (grade + 1) _ mode))

/-- Dense-core continuity identifies native Theta's genuine angular trace
with the accepted completed psi, without discarding its extra grade. -/
theorem completedNativeThetaTrace_angular (grade : ℕ) (large : 1 ≤ grade)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    matchingAngular L sigma gamma ell (grade + 1) (completedNativeThetaTrace admissible grade core field) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) (completedPsi admissible grade core field) := by
  let first := (matchingAngular L sigma gamma ell (grade + 1)).comp (completedNativeThetaTrace admissible grade core)
  let second := (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)).comp (completedPsi admissible grade core)
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade core)
    (isClosed_eq first.continuous second.continuous) _ field
  intro source
  change matchingAngular L sigma gamma ell (grade + 1)
    (apBoundaryTrace L sigma gamma ell (grade + 2) (by omega) (source.val.1.val (grade + 2))) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedPsi admissible grade core (compensatedIntoClosure admissible grade core source))
  rw [completedPsi_core]
  exact matchingAngular_smooth admissible (grade + 1) (by omega) source.val.1

theorem completedStrongScalar_weak (grade : ℕ) (large : 1 ≤ grade)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    strongMatchingWeak L sigma gamma ell (grade + 1) (completedStrongScalar admissible grade core field) =
      (ell : ℂ)⁻¹ • apHighProjection L sigma gamma ell (grade + 1)
        (completedMatchingD admissible grade core field) := by
  have angular := strongMatchingWeak_angular L sigma gamma ell (grade + 1)
    (completedNativeThetaTrace admissible grade core field)
  have scalar := congrArg (apHighProjection L sigma gamma ell (grade + 1))
    (completedNativeThetaTrace_angular admissible grade large core field)
  let psiTrace := apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
    (completedPsi admissible grade core field)
  have scaling := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => (ell : ℂ)⁻¹ • value)
    ((apHighProjection L sigma gamma ell (grade + 1)).map_smul (ell : ℂ) psiTrace)
  have cancel := inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr admissible.2.2.2.1.ne')
    (apHighProjection L sigma gamma ell (grade + 1) psiTrace)
  exact angular.trans (scalar.trans (scaling.trans cancel).symm)

theorem completedStrongFlux_weak (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    strongMatchingWeak L sigma gamma ell grade (completedStrongFlux admissible data grade core field) =
      apHighProjection L sigma gamma ell grade (completedMatchingX admissible data grade core field) :=
  strongMatchingWeak_angular L sigma gamma ell grade (completedMatchingP admissible data grade core field)

/-- Literal smooth-core scalar coefficients: R is the genuine Cartesian rotation. -/
theorem completedStrongScalar_core (grade : ℕ) (large : 1 ≤ grade)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell (grade + 1)
      (completedStrongScalar admissible grade core (compensatedIntoClosure admissible grade core field)) mode =
      if 3 ≤ |mode.1| then
        fourierCoeff (fun angle : CellCircle =>
          (apSmoothJet admissible 1 mode.2 (apSmoothRotation admissible 1 field.val.1)).value (boundaryDiskPoint angle)) mode.1
      else 0 := by
  have weak := (strongMatchingWeak_angular L sigma gamma ell (grade + 1)
    (completedNativeThetaTrace admissible grade core (compensatedIntoClosure admissible grade core field))).trans
      (congrArg (apHighProjection L sigma gamma ell (grade + 1))
        (completedNativeThetaTrace_angular admissible grade large core _))
  have coefficient := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) =>
    apBoundaryCoefficient L sigma gamma ell (grade + 1) value mode) weak
  have corePsi := congrArg (fun psi : apGrade L sigma gamma ell 1 (grade + 1) =>
    apBoundaryCoefficient L sigma gamma ell (grade + 1)
      (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) psi) mode)
    (completedPsi_core admissible grade core field)
  have endpoint := corePsi.trans (matchingSmoothTrace_coefficient admissible (grade + 1) (by omega)
    (apSmoothRotation admissible 1 field.val.1) mode)
  have projected := apHighProjection_coefficient L sigma gamma ell (grade + 1)
    (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (completedPsi admissible grade core (compensatedIntoClosure admissible grade core field))) mode
  have weakCoefficient := strongMatchingWeak_coefficient L sigma gamma ell (grade + 1) (by omega)
    (completedStrongScalar admissible grade core (compensatedIntoClosure admissible grade core field)) mode
  exact weakCoefficient.symm.trans (coefficient.trans
    (projected.trans (congrArg (fun value : ComplexEuclidean 1 => if 3 ≤ |mode.1| then value else 0) endpoint)))

/-- Literal smooth-core angular flux of the actual AR8 two-term primitive. -/
theorem completedStrongFlux_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (large : 2 ≤ grade) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell grade
      (completedStrongFlux admissible data grade core (compensatedIntoClosure admissible grade core field)) mode =
      if 3 ≤ |mode.1| then
        fourierCoeff (fun angle : CellCircle =>
          (apSmoothJet admissible 1 mode.2
            (apSmoothRotation admissible 1 (smoothMatchingPrimitive admissible data coherent field.val))).value
              (boundaryDiskPoint angle)) mode.1
      else 0 := by
  have coefficient := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 grade =>
    apBoundaryCoefficient L sigma gamma ell grade value mode)
      (completedStrongFlux_weak admissible data grade core (compensatedIntoClosure admissible grade core field))
  have coreFlux := congrArg (fun boundary : APBoundaryGrade L sigma gamma ell 1 grade =>
    apBoundaryCoefficient L sigma gamma ell grade boundary mode)
    (completedMatchingX_core admissible data coherent grade large core field)
  have endpoint := coreFlux.trans (matchingSmoothTrace_coefficient admissible grade large
    (apSmoothRotation admissible 1 (smoothMatchingPrimitive admissible data coherent field.val)) mode)
  have projected := apHighProjection_coefficient L sigma gamma ell grade
    (completedMatchingX admissible data grade core (compensatedIntoClosure admissible grade core field)) mode
  have weakCoefficient := strongMatchingWeak_coefficient L sigma gamma ell grade (by omega)
    (completedStrongFlux admissible data grade core (compensatedIntoClosure admissible grade core field)) mode
  exact weakCoefficient.symm.trans (coefficient.trans
    (projected.trans (congrArg (fun value : ComplexEuclidean 1 => if 3 ≤ |mode.1| then value else 0) endpoint)))

end Grad.GaugeCoefficients.Physical.Compensated
