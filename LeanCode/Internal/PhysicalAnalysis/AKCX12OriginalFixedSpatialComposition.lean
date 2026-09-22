import AKCX11ActualFixedSpatialActions
import AKBW16OriginalPrincipalRankTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges Grad.ActualAngularInverse
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction
variable {L ell : ℝ}

def value {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output) : StartupSpatialAction rank input output L ell :=
  point rank mapping (LinearIsometryEquiv.refl ℝ _)

def character (dimension rank : ℕ) (mode : ℤ) : StartupSpatialAction rank dimension dimension L ell :=
  angular dimension rank (angularCharacter mode) (angularCharacter_smooth mode)

def primitive (dimension rank : ℕ) (shift : ℤ) : StartupSpatialAction rank dimension dimension L ell :=
  angular dimension rank (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

def trueAngular (dimension rank : ℕ) (shift : ℤ) : StartupSpatialAction rank dimension dimension L ell :=
  (primitive dimension rank shift).comp ((identity rank dimension).sub (character dimension rank (-shift)))

def average (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  ((value rank positiveHelicity).comp (character 2 rank 1)).add
    ((value rank negativeHelicity).comp (character 2 rank (-1)))

def tangential (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  (((identity rank 2).sub (point rank reflectionValueMap cartesianReflectionEquiv)).comp (average rank)).smul (1/2)

def complement (rank : ℕ) : StartupSpatialAction rank 3 3 L ell :=
  ((value rank planarInclusionMap).comp ((tangential rank).comp (value rank planarPartMap))).add
    ((value rank toroidalInclusionMap).comp ((character 1 rank 0).comp (value rank toroidalPartMap)))

def circle (rank : ℕ) : StartupSpatialAction rank 3 3 L ell := (identity rank 3).sub (complement rank)

def planarMeanFree (rank : ℕ) : StartupSpatialAction rank 2 2 L ell := (identity rank 2).sub (average rank)

def scalarMeanFree (rank : ℕ) : StartupSpatialAction rank 1 1 L ell := (identity rank 1).sub (character 1 rank 0)

def covariantInverse (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  ((trueAngular 2 rank (-1)).comp (value rank positiveHelicity)).add
    ((trueAngular 2 rank 1).comp (value rank negativeHelicity))

def scalarInverse (rank : ℕ) : StartupSpatialAction rank 1 1 L ell := trueAngular 1 rank 0

def gradientRecovery (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  (planarMeanFree rank).add (((covariantInverse rank).comp (value rank quarterValueMap)).smul 2)

def radial (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  (identity rank 2).add ((value rank quarterValueMap).comp ((tangential rank).comp (value rank quarterValueMap)))

def inverseCovector (rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : StartupSpatialAction rank 3 3 L ell :=
  angular 3 rank (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

def trueInverseTensor (rank : ℕ) (input output : Fin 2) : StartupSpatialAction rank 3 3 L ell :=
  (inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).comp
      (inverseCovector rank (angularCharacter 0) (angularCharacter_smooth 0) input 0)).add
    ((inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output).comp
      (inverseCovector rank (angularCharacter 0) (angularCharacter_smooth 0) input 1)))

def principalFixed (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) : StartupSpatialAction rank 3 3 L ell :=
  ![((value rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 0 inner)).sub
      ((value rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 1 inner)),
    if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0,
    (value rank (startupPlanarEntryMap outer inner)).sub
      ((((value rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 0 inner)).add
        ((value rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 1 inner))).smul 2)] row

theorem complement_ranked (rank : ℕ) :
    (complement (L := L) (ell := ell) rank).ranked = StartupRankOperator.complement rank := rfl

theorem principalFixed_ranked (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed (L := L) (ell := ell) rank outer inner row).ranked =
      StartupRankOperator.principalFixed rank outer inner row := by
  fin_cases row
  · rfl
  · change (if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).ranked = _
    change (if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).ranked =
      if outer = inner then StartupRankOperator.trueAngular 3 rank 0 else (StartupRankOperator.identity rank 3).smul 0
    split_ifs <;> rfl
  · rfl

theorem complement_coarse (rank : ℕ) :
    (complement (L := L) (ell := ell) rank).signed.coarse = originalComplementKernel := rfl

theorem radial_coarse (rank : ℕ) :
    (radial (L := L) (ell := ell) rank).signed.coarse = startupGenuineQradKernel := rfl

theorem trueInverseTensor_coarse (rank : ℕ) (input output : Fin 2) :
    (trueInverseTensor (L := L) (ell := ell) rank input output).signed.coarse = startupTrueInverseTensorKernel input output := by
  unfold startupTrueInverseTensorKernel
  rw [Fin.sum_univ_two]
  rfl

theorem principalFixed_coarse (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed (L := L) (ell := ell) rank outer inner row).signed.coarse = startupPrincipalFixedKernel outer inner row := by
  fin_cases row
  · change (originalValueKernel (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 0 inner).signed.coarse -
      (originalValueKernel (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 1 inner).signed.coarse = _
    rw [trueInverseTensor_coarse,trueInverseTensor_coarse]
    rfl
  · change (if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).signed.coarse =
      if outer = inner then startupTrueAngularInverse 3 0 else 0
    split_ifs
    · rfl
    · change (0 : ℂ) • (ContinuousLinearMap.id ℂ (StartupL2 3)) = 0
      exact zero_smul _ _
  · change originalValueKernel (startupPlanarEntryMap outer inner) -
      (2 : ℂ) • (((originalValueKernel (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 0 inner).signed.coarse) +
        ((originalValueKernel (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 1 inner).signed.coarse)) =
      originalValueKernel (startupPlanarEntryMap outer inner) - (2 : ℂ) •
        ∑ middle : Fin 2, (originalValueKernel (startupPlanarRotatedEntryMap outer middle)).comp (startupTrueInverseTensorKernel middle inner)
    rw [trueInverseTensor_coarse,trueInverseTensor_coarse,Fin.sum_univ_two]

end StartupSpatialAction
end Grad.CartesianStartup
