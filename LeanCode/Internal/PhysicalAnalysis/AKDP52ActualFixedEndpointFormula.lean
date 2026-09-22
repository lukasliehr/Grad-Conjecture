import AKDP51ActualFixedCellEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualAngularInverse Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction
variable {L ell : ℝ}

theorem value_originalEndpointControlled {input output : ℕ} (parameters : PhaseParameters) (rank : ℕ)
    (mapping : OperatorValue input output) :
    (value (L := L) (ell := ell) rank mapping).OriginalEndpointControlled parameters :=
  point_originalEndpointControlled parameters rank mapping (LinearIsometryEquiv.refl ℝ _)

theorem character_originalEndpointControlled (parameters : PhaseParameters) (dimension rank : ℕ) (mode : ℤ) :
    (character (L := L) (ell := ell) dimension rank mode).OriginalEndpointControlled parameters :=
  angular_originalEndpointControlled parameters dimension rank (angularCharacter mode) (angularCharacter_smooth mode)

theorem primitive_originalEndpointControlled (parameters : PhaseParameters) (dimension rank : ℕ) (shift : ℤ) :
    (primitive (L := L) (ell := ell) dimension rank shift).OriginalEndpointControlled parameters :=
  angular_originalEndpointControlled parameters dimension rank (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

theorem trueAngular_originalEndpointControlled (parameters : PhaseParameters) (dimension rank : ℕ) (shift : ℤ) :
    (trueAngular (L := L) (ell := ell) dimension rank shift).OriginalEndpointControlled parameters :=
  (primitive_originalEndpointControlled parameters dimension rank shift).comp
    ((identity_originalEndpointControlled parameters rank dimension).sub (character_originalEndpointControlled parameters dimension rank (-shift)))

theorem average_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (average (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  ((value_originalEndpointControlled parameters rank positiveHelicity).comp (character_originalEndpointControlled parameters 2 rank 1)).add
    ((value_originalEndpointControlled parameters rank negativeHelicity).comp (character_originalEndpointControlled parameters 2 rank (-1)))

theorem tangential_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (tangential (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (((identity_originalEndpointControlled parameters rank 2).sub (point_originalEndpointControlled parameters rank reflectionValueMap cartesianReflectionEquiv)).comp
    (average_originalEndpointControlled parameters rank)).smul (1/2)

theorem complement_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (complement (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  ((value_originalEndpointControlled parameters rank planarInclusionMap).comp
    ((tangential_originalEndpointControlled parameters rank).comp (value_originalEndpointControlled parameters rank planarPartMap))).add
  ((value_originalEndpointControlled parameters rank toroidalInclusionMap).comp
    ((character_originalEndpointControlled parameters 1 rank 0).comp (value_originalEndpointControlled parameters rank toroidalPartMap)))

theorem circle_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (circle (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (identity_originalEndpointControlled parameters rank 3).sub (complement_originalEndpointControlled parameters rank)

theorem planarMeanFree_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (planarMeanFree (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (identity_originalEndpointControlled parameters rank 2).sub (average_originalEndpointControlled parameters rank)

theorem scalarMeanFree_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (scalarMeanFree (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (identity_originalEndpointControlled parameters rank 1).sub (character_originalEndpointControlled parameters 1 rank 0)

theorem radial_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (radial (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (identity_originalEndpointControlled parameters rank 2).add
    ((value_originalEndpointControlled parameters rank quarterValueMap).comp
      ((tangential_originalEndpointControlled parameters rank).comp (value_originalEndpointControlled parameters rank quarterValueMap)))

theorem inverseCovector_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) (direction coordinate : Fin 2) :
    (inverseCovector (L := L) (ell := ell) rank weight smooth direction coordinate).OriginalEndpointControlled parameters :=
  angular_originalEndpointControlled parameters 3 rank (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

theorem trueInverseTensor_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) (input output : Fin 2) :
    (trueInverseTensor (L := L) (ell := ell) rank input output).OriginalEndpointControlled parameters :=
  (inverseCovector_originalEndpointControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((inverseCovector_originalEndpointControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).comp
      (inverseCovector_originalEndpointControlled parameters rank (angularCharacter 0) (angularCharacter_smooth 0) input 0)).add
    ((inverseCovector_originalEndpointControlled parameters rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output).comp
      (inverseCovector_originalEndpointControlled parameters rank (angularCharacter 0) (angularCharacter_smooth 0) input 1)))

theorem principalFixed_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed (L := L) (ell := ell) rank outer inner row).OriginalEndpointControlled parameters := by
  fin_cases row
  · exact ((value_originalEndpointControlled parameters rank (startupPlanarRotatedEntryMap outer 1)).comp
      (trueInverseTensor_originalEndpointControlled parameters rank 0 inner)).sub
      ((value_originalEndpointControlled parameters rank (startupPlanarRotatedEntryMap outer 0)).comp
      (trueInverseTensor_originalEndpointControlled parameters rank 1 inner))
  · change (if outer=inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).OriginalEndpointControlled parameters
    split_ifs
    · exact trueAngular_originalEndpointControlled parameters 3 rank 0
    · exact (identity_originalEndpointControlled parameters rank 3).smul 0
  · exact (value_originalEndpointControlled parameters rank (startupPlanarEntryMap outer inner)).sub
      ((((value_originalEndpointControlled parameters rank (startupPlanarRotatedEntryMap outer 0)).comp
        (trueInverseTensor_originalEndpointControlled parameters rank 0 inner)).add
        ((value_originalEndpointControlled parameters rank (startupPlanarRotatedEntryMap outer 1)).comp
        (trueInverseTensor_originalEndpointControlled parameters rank 1 inner))).smul 2)

end StartupSpatialAction
end Grad.CartesianStartup
