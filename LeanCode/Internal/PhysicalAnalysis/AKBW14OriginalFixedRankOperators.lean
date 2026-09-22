import AKBW13FullMatrixRankLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.Constraints Grad.Constraints.Gauges Grad.ActualAngularInverse

namespace StartupRankOperator

def value {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output) :=
  point rank mapping (LinearIsometryEquiv.refl ℝ _)

def character (dimension rank : ℕ) (mode : ℤ) :=
  angular dimension rank (angularCharacter mode) (angularCharacter_smooth mode)

def primitive (dimension rank : ℕ) (shift : ℤ) :=
  angular dimension rank (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

def trueAngular (dimension rank : ℕ) (shift : ℤ) :=
  (primitive dimension rank shift).comp ((identity rank dimension).sub (character dimension rank (-shift)))

def average (rank : ℕ) : StartupRankOperator rank 2 2 :=
  ((value rank positiveHelicity).comp (character 2 rank 1)).add
    ((value rank negativeHelicity).comp (character 2 rank (-1)))

def tangential (rank : ℕ) : StartupRankOperator rank 2 2 :=
  (((identity rank 2).sub (point rank reflectionValueMap cartesianReflectionEquiv)).comp (average rank)).smul (1 / 2)

def complement (rank : ℕ) : StartupRankOperator rank 3 3 :=
  ((value rank planarInclusionMap).comp ((tangential rank).comp (value rank planarPartMap))).add
    ((value rank toroidalInclusionMap).comp ((character 1 rank 0).comp (value rank toroidalPartMap)))

def circle (rank : ℕ) : StartupRankOperator rank 3 3 := (identity rank 3).sub (complement rank)

def planarMeanFree (rank : ℕ) : StartupRankOperator rank 2 2 := (identity rank 2).sub (average rank)

def scalarMeanFree (rank : ℕ) : StartupRankOperator rank 1 1 := (identity rank 1).sub (character 1 rank 0)

def covariantInverse (rank : ℕ) : StartupRankOperator rank 2 2 :=
  ((trueAngular 2 rank (-1)).comp (value rank positiveHelicity)).add
    ((trueAngular 2 rank 1).comp (value rank negativeHelicity))

def scalarInverse (rank : ℕ) : StartupRankOperator rank 1 1 := trueAngular 1 rank 0

def gradientRecovery (rank : ℕ) : StartupRankOperator rank 2 2 :=
  (planarMeanFree rank).add (((covariantInverse rank).comp (value rank quarterValueMap)).smul 2)

/-- The genuine radial projector I+JTJ, including the reflected covectors. -/
def radial (rank : ℕ) : StartupRankOperator rank 2 2 :=
  (identity rank 2).add ((value rank quarterValueMap).comp ((tangential rank).comp (value rank quarterValueMap)))

theorem value_bound_independent {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output) :
    (value rank mapping).bound = (value 0 mapping).bound := rfl

theorem character_bound_independent (dimension rank : ℕ) (mode : ℤ) :
    (character dimension rank mode).bound = (character dimension 0 mode).bound := rfl

theorem complement_bound_independent (rank : ℕ) : (complement rank).bound = (complement 0).bound := rfl

theorem radial_bound_independent (rank : ℕ) : (radial rank).bound = (radial 0).bound := rfl

theorem covariantInverse_bound_independent (rank : ℕ) :
    (covariantInverse rank).bound = (covariantInverse 0).bound := rfl

theorem scalarInverse_bound_independent (rank : ℕ) :
    (scalarInverse rank).bound = (scalarInverse 0).bound := rfl

end StartupRankOperator
end Grad.CartesianStartup
