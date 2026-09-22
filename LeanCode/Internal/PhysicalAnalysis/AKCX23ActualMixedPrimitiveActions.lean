import AKCX22ActualMixedComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges Grad.ActualAngularInverse
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction
variable {L ell : ℝ}

theorem identity_mixed (rank dimension : ℕ) : (identity (L := L) (ell := ell) rank dimension).HasMixedLeading :=
  mixed_of_sameMoment _ (fun _ _ => rfl)

theorem point_mixed {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : (point (L := L) (ell := ell) rank mapping orthogonal).HasMixedLeading :=
  mixed_of_sameMoment _ (fun _ _ => rfl)

theorem angular_mixed (dimension rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    (angular (L := L) (ell := ell) dimension rank weight smooth).HasMixedLeading :=
  mixed_of_sameMoment _ (fun _ _ => rfl)

theorem matrix_mixed {sigma gamma : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ) (coefficients : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent coefficients) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) :
    (matrix admissible rank coefficients coherent lengthNonzero scaleNonzero).HasMixedLeading := by
  intro family regular power lower
  exact startupActualMatrix_mixedRankFirst admissible coefficients coherent lengthNonzero scaleNonzero family regular power lower

theorem value_mixed {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output) :
    (value (L := L) (ell := ell) rank mapping).HasMixedLeading := point_mixed rank mapping _

theorem character_mixed (dimension rank : ℕ) (mode : ℤ) :
    (character (L := L) (ell := ell) dimension rank mode).HasMixedLeading := angular_mixed dimension rank _ _

theorem primitive_mixed (dimension rank : ℕ) (shift : ℤ) :
    (primitive (L := L) (ell := ell) dimension rank shift).HasMixedLeading := angular_mixed dimension rank _ _

theorem trueAngular_mixed (dimension rank : ℕ) (shift : ℤ) :
    (trueAngular (L := L) (ell := ell) dimension rank shift).HasMixedLeading :=
  (primitive_mixed dimension rank shift).comp ((identity_mixed rank dimension).sub (character_mixed dimension rank (-shift)))

theorem average_mixed (rank : ℕ) : (average (L := L) (ell := ell) rank).HasMixedLeading :=
  ((value_mixed rank positiveHelicity).comp (character_mixed 2 rank 1)).add
    ((value_mixed rank negativeHelicity).comp (character_mixed 2 rank (-1)))

theorem tangential_mixed (rank : ℕ) : (tangential (L := L) (ell := ell) rank).HasMixedLeading :=
  (((identity_mixed rank 2).sub (point_mixed rank reflectionValueMap cartesianReflectionEquiv)).comp (average_mixed rank)).smul (1/2)

theorem complement_mixed (rank : ℕ) : (complement (L := L) (ell := ell) rank).HasMixedLeading :=
  ((value_mixed rank planarInclusionMap).comp ((tangential_mixed rank).comp (value_mixed rank planarPartMap))).add
    ((value_mixed rank toroidalInclusionMap).comp ((character_mixed 1 rank 0).comp (value_mixed rank toroidalPartMap)))

theorem circle_mixed (rank : ℕ) : (circle (L := L) (ell := ell) rank).HasMixedLeading :=
  (identity_mixed rank 3).sub (complement_mixed rank)

theorem planarMeanFree_mixed (rank : ℕ) : (planarMeanFree (L := L) (ell := ell) rank).HasMixedLeading :=
  (identity_mixed rank 2).sub (average_mixed rank)

theorem scalarMeanFree_mixed (rank : ℕ) : (scalarMeanFree (L := L) (ell := ell) rank).HasMixedLeading :=
  (identity_mixed rank 1).sub (character_mixed 1 rank 0)

theorem radial_mixed (rank : ℕ) : (radial (L := L) (ell := ell) rank).HasMixedLeading :=
  (identity_mixed rank 2).add ((value_mixed rank quarterValueMap).comp ((tangential_mixed rank).comp (value_mixed rank quarterValueMap)))

theorem inverseCovector_mixed (rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) (direction coordinate : Fin 2) :
    (inverseCovector (L := L) (ell := ell) rank weight smooth direction coordinate).HasMixedLeading := angular_mixed 3 rank _ _

theorem trueInverseTensor_mixed (rank : ℕ) (input output : Fin 2) :
    (trueInverseTensor (L := L) (ell := ell) rank input output).HasMixedLeading :=
  (inverseCovector_mixed rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((inverseCovector_mixed rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).comp
      (inverseCovector_mixed rank (angularCharacter 0) (angularCharacter_smooth 0) input 0)).add
    ((inverseCovector_mixed rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output).comp
      (inverseCovector_mixed rank (angularCharacter 0) (angularCharacter_smooth 0) input 1)))

theorem principalFixed_mixed (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed (L := L) (ell := ell) rank outer inner row).HasMixedLeading := by
  fin_cases row
  · exact ((value_mixed rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor_mixed rank 0 inner)).sub
      ((value_mixed rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor_mixed rank 1 inner))
  · change (if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).HasMixedLeading
    split_ifs
    · exact trueAngular_mixed 3 rank 0
    · exact (identity_mixed rank 3).smul 0
  · exact (value_mixed rank (startupPlanarEntryMap outer inner)).sub
      ((((value_mixed rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor_mixed rank 0 inner)).add
        ((value_mixed rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor_mixed rank 1 inner))).smul 2)

end StartupSpatialAction
end Grad.CartesianStartup
