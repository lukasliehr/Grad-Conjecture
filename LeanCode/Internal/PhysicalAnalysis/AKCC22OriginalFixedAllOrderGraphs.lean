import AKCC21ActualGraphActionAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.Constraints Grad.Constraints.Gauges Grad.ActualAngularInverse
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupCharacter_preservesGraph (dimension : ℕ) (mode : ℤ) :
    StartupPreservesGraph (startupCharacterKernel dimension mode) :=
  startupAngular_preservesGraph dimension (angularCharacter mode) (angularCharacter_smooth mode)

theorem startupPrimitive_preservesGraph (dimension : ℕ) (shift : ℤ) :
    StartupPreservesGraph (startupPrimitiveKernel dimension shift) :=
  startupAngular_preservesGraph dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

theorem startupTrueAngular_preservesGraph (dimension : ℕ) (shift : ℤ) :
    StartupPreservesGraph (startupTrueAngularInverse dimension shift) :=
  (startupPrimitive_preservesGraph dimension shift).comp
    ((StartupPreservesGraph.identity dimension).sub (startupCharacter_preservesGraph dimension (-shift)))

theorem originalValue_preservesGraph {input output : ℕ} (mapping : OperatorValue input output) :
    StartupPreservesGraph (originalValueKernel mapping) :=
  startupPoint_preservesGraph mapping (LinearIsometryEquiv.refl ℝ _)

theorem originalAverage_preservesGraph : StartupPreservesGraph originalAverageKernel :=
  ((originalValue_preservesGraph positiveHelicity).comp (startupCharacter_preservesGraph 2 1)).add
    ((originalValue_preservesGraph negativeHelicity).comp (startupCharacter_preservesGraph 2 (-1)))

theorem originalTangential_preservesGraph : StartupPreservesGraph originalTangentialKernel :=
  (((StartupPreservesGraph.identity 2).sub
    (startupPoint_preservesGraph reflectionValueMap cartesianReflectionEquiv)).comp originalAverage_preservesGraph).smul (1 / 2)

theorem originalComplement_preservesGraph : StartupPreservesGraph originalComplementKernel :=
  ((originalValue_preservesGraph planarInclusionMap).comp
    (originalTangential_preservesGraph.comp (originalValue_preservesGraph planarPartMap))).add
    ((originalValue_preservesGraph toroidalInclusionMap).comp
      ((startupCharacter_preservesGraph 1 0).comp (originalValue_preservesGraph toroidalPartMap)))

theorem originalCircle_preservesGraph : StartupPreservesGraph originalCircleKernel :=
  (StartupPreservesGraph.identity 3).sub originalComplement_preservesGraph

theorem originalPlanarMeanFree_preservesGraph : StartupPreservesGraph originalPlanarMeanFreeKernel :=
  (StartupPreservesGraph.identity 2).sub originalAverage_preservesGraph

theorem originalScalarMeanFree_preservesGraph : StartupPreservesGraph originalScalarMeanFreeKernel :=
  (StartupPreservesGraph.identity 1).sub (startupCharacter_preservesGraph 1 0)

theorem originalCovariantInverse_preservesGraph : StartupPreservesGraph originalCovariantInverseKernel :=
  ((startupTrueAngular_preservesGraph 2 (-1)).comp (originalValue_preservesGraph positiveHelicity)).add
    ((startupTrueAngular_preservesGraph 2 1).comp (originalValue_preservesGraph negativeHelicity))

theorem originalScalarInverse_preservesGraph : StartupPreservesGraph originalScalarInverseKernel :=
  startupTrueAngular_preservesGraph 1 0

theorem originalGradientRecovery_preservesGraph : StartupPreservesGraph originalGradientRecoveryKernel :=
  originalPlanarMeanFree_preservesGraph.add
    ((originalCovariantInverse_preservesGraph.comp (originalValue_preservesGraph quarterValueMap)).smul 2)

theorem startupGenuineQrad_preservesGraph : StartupPreservesGraph startupGenuineQradKernel :=
  (StartupPreservesGraph.identity 2).add ((originalValue_preservesGraph quarterValueMap).comp
    (originalTangential_preservesGraph.comp (originalValue_preservesGraph quarterValueMap)))

end Grad.CartesianStartup
