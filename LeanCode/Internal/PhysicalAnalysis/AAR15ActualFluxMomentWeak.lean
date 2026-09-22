import AAR14ScalarMomentFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Flux
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularUncorrectedFluxMoment (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  annularRadialMoment lower positive
    (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode) -
  annularRadialMoment lower positive (source.1 mode)

def annularUncorrectedFluxMomentRHS (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
    (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
  collarScalar 1 lower (annularPotentialCurve lower length positive mode)
    (annularRadialMoment lower positive (annularEnergyValue lower length positive field mode)) -
  collarScalar 1 lower (annularRadialCurve lower positive) (annularRadialMoment lower positive (source.1 mode)) -
  annularDSymbol mode • annularRadialMoment lower positive (source.2.1 mode) -
  annularCellSymbol length mode • annularRadialMoment lower positive (source.2.2.1 mode)

/-- The weak derivative of r(e^Phi xi_r-e^Phi f) follows from the
actual variational solution, using only genuine compact smooth tests. -/
theorem annularUncorrectedFluxMoment_weak (bounded : lower < 1)
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CompactWeakDerivative 1 lower
      (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode)
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) := by
  dsimp only
  intro profile smooth _compact supported vector
  let test := collarCompactTest lower profile smooth supported
  have law := annularVariationalSolution_scalar_test parameters lower length positive bounded lengthPositive widthHalf widthLength
    source innerValue mode profile smooth test.lowerZero vector
  rw [annularForm_scalar_moment, annularFunctional_scalar_moment] at law
  dsimp only at law
  have outerZero : profile 1 = 0 := test.upperZero
  simp only [outerZero, zero_smul, smul_zero, inner_zero_left, add_zero, sub_zero] at law
  simp only [annularUncorrectedFluxMomentRHS, annularUncorrectedFluxMoment, map_add, map_sub] at law ⊢
  linear_combination law

theorem annularRecoveredQ_moment (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (source : AnnularForcing lower) (mode : HighAnnularMode) :
    annularRadialMoment lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) =
      annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode +
        (2 : ℝ) • annularOrdinaryCoordinate lower length positive bounded mode 0 field := by
  change annularRadialMoment lower positive
    (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode +
      annularEnergyRadial lower length positive field mode - source.1 mode) = _
  rw [map_sub, map_add, annularRadialMoment_radial lower length positive bounded mode field]
  unfold annularUncorrectedFluxMoment
  abel

def annularFluxMomentRHS (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode +
    (2 : ℝ) • annularOrdinaryCoordinate lower length positive bounded mode 1 field

/-- Genuine weak first-order flux regularity without differentiating f.
The value is exactly r e^Phi q, with q from the original first row. -/
theorem annularRecoveredQ_moment_weak (bounded : lower < 1)
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CompactWeakDerivative 1 lower
      (annularRadialMoment lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode))
      (annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) := by
  dsimp only
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have first := annularUncorrectedFluxMoment_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode
  have second := collarWeak_isCompact 1 lower _ _
    (annularModeRadialH1_weak lower length positive bounded.le mode field)
  intro profile smooth compact supported vector
  have firstLaw := first profile smooth compact supported vector
  have secondLaw := second profile smooth compact supported vector
  change collarPairing lower _ vector
      (annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) = _
  rw [annularRecoveredQ_moment parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode]
  simp only [annularFluxMomentRHS, map_add, map_smul]
  change collarPairing lower _ vector
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
      (2 : ℂ) * collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 1 field) = -(collarPairing lower _ vector
    (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
      (2 : ℂ) * collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 0 field))
  change collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 1 field) =
    -collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 0 field) at secondLaw
  linear_combination firstLaw + 2 * secondLaw

end Flux
end Grad.AnnularReconstruction
