import AKDP26FixedSpatialCoreRankControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualAngularInverse Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction
variable {L ell : ℝ}

theorem value_originalRankControlled {input output : ℕ} (parameters : PhaseParameters) (rank : ℕ)
    (mapping : OperatorValue input output) :
    (value (L := L) (ell := ell) rank mapping).OriginalRankControlled parameters :=
  point_originalRankControlled parameters rank mapping (LinearIsometryEquiv.refl ℝ _)

theorem character_originalRankControlled (parameters : PhaseParameters) (dimension rank : ℕ) (mode : ℤ) :
    (character (L := L) (ell := ell) dimension rank mode).OriginalRankControlled parameters :=
  angular_originalRankControlled parameters dimension rank (angularCharacter mode) (angularCharacter_smooth mode)

theorem primitive_originalRankControlled (parameters : PhaseParameters) (dimension rank : ℕ) (shift : ℤ) :
    (primitive (L := L) (ell := ell) dimension rank shift).OriginalRankControlled parameters :=
  angular_originalRankControlled parameters dimension rank (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

theorem trueAngular_originalRankControlled (parameters : PhaseParameters) (dimension rank : ℕ) (shift : ℤ) :
    (trueAngular (L := L) (ell := ell) dimension rank shift).OriginalRankControlled parameters :=
  (primitive_originalRankControlled parameters dimension rank shift).comp
    ((identity_originalRankControlled parameters rank dimension).sub (character_originalRankControlled parameters dimension rank (-shift)))

theorem average_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (average (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  ((value_originalRankControlled parameters rank positiveHelicity).comp (character_originalRankControlled parameters 2 rank 1)).add
    ((value_originalRankControlled parameters rank negativeHelicity).comp (character_originalRankControlled parameters 2 rank (-1)))

theorem tangential_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (tangential (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  (((identity_originalRankControlled parameters rank 2).sub (point_originalRankControlled parameters rank reflectionValueMap cartesianReflectionEquiv)).comp
    (average_originalRankControlled parameters rank)).smul (1/2)

theorem complement_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (complement (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  ((value_originalRankControlled parameters rank planarInclusionMap).comp
    ((tangential_originalRankControlled parameters rank).comp (value_originalRankControlled parameters rank planarPartMap))).add
  ((value_originalRankControlled parameters rank toroidalInclusionMap).comp
    ((character_originalRankControlled parameters 1 rank 0).comp (value_originalRankControlled parameters rank toroidalPartMap)))

theorem circle_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (circle (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  (identity_originalRankControlled parameters rank 3).sub (complement_originalRankControlled parameters rank)

theorem planarMeanFree_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (planarMeanFree (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  (identity_originalRankControlled parameters rank 2).sub (average_originalRankControlled parameters rank)

theorem scalarMeanFree_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (scalarMeanFree (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  (identity_originalRankControlled parameters rank 1).sub (character_originalRankControlled parameters 1 rank 0)

theorem radial_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) :
    (radial (L := L) (ell := ell) rank).OriginalRankControlled parameters :=
  (identity_originalRankControlled parameters rank 2).add
    ((value_originalRankControlled parameters rank quarterValueMap).comp
      ((tangential_originalRankControlled parameters rank).comp (value_originalRankControlled parameters rank quarterValueMap)))

theorem inverseCovector_originalRankControlled (parameters : PhaseParameters) (rank : ℕ)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) (direction coordinate : Fin 2) :
    (inverseCovector (L := L) (ell := ell) rank weight smooth direction coordinate).OriginalRankControlled parameters :=
  angular_originalRankControlled parameters 3 rank (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

theorem trueInverseTensor_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) (input output : Fin 2) :
    (trueInverseTensor (L := L) (ell := ell) rank input output).OriginalRankControlled parameters :=
  (inverseCovector_originalRankControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((inverseCovector_originalRankControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).comp
      (inverseCovector_originalRankControlled parameters rank (angularCharacter 0) (angularCharacter_smooth 0) input 0)).add
    ((inverseCovector_originalRankControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output).comp
      (inverseCovector_originalRankControlled parameters rank (angularCharacter 0) (angularCharacter_smooth 0) input 1)))

theorem principalFixed_originalRankControlled (parameters : PhaseParameters) (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed (L := L) (ell := ell) rank outer inner row).OriginalRankControlled parameters := by
  fin_cases row
  · exact ((value_originalRankControlled parameters rank (startupPlanarRotatedEntryMap outer 1)).comp
      (trueInverseTensor_originalRankControlled parameters rank 0 inner)).sub
      ((value_originalRankControlled parameters rank (startupPlanarRotatedEntryMap outer 0)).comp
      (trueInverseTensor_originalRankControlled parameters rank 1 inner))
  · change (if outer=inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).OriginalRankControlled parameters
    split_ifs
    · exact trueAngular_originalRankControlled parameters 3 rank 0
    · exact (identity_originalRankControlled parameters rank 3).smul 0
  · exact (value_originalRankControlled parameters rank (startupPlanarEntryMap outer inner)).sub
      ((((value_originalRankControlled parameters rank (startupPlanarRotatedEntryMap outer 0)).comp
        (trueInverseTensor_originalRankControlled parameters rank 0 inner)).add
        ((value_originalRankControlled parameters rank (startupPlanarRotatedEntryMap outer 1)).comp
        (trueInverseTensor_originalRankControlled parameters rank 1 inner))).smul 2)

end StartupSpatialAction
end Grad.CartesianStartup
