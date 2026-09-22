import AKAA28FixedGraphCompatibility

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GenericCarriers

def originalValueFirstGraph {input output : ℕ} (mapping : OperatorValue input output) :
    StartupFirst input →L[ℂ] StartupFirst output :=
  startupPointFirstGraph mapping (LinearIsometryEquiv.refl ℝ _)

/-- The actual equivariant average, with both helicity projectors. -/
def originalAverageFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  (originalValueFirstGraph positiveHelicity).comp (startupCharacterFirstGraph 2 1) +
    (originalValueFirstGraph negativeHelicity).comp (startupCharacterFirstGraph 2 (-1))

/-- The nonsingular reflection formula for the true tangential gauge T. -/
def originalTangentialFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  (1 / 2 : ℂ) • ((ContinuousLinearMap.id ℂ _ -
    startupPointFirstGraph reflectionValueMap cartesianReflectionEquiv).comp originalAverageFirstGraph)

/-- Literal C0=diag(T,Pi) on the full integer-cell L2 space. -/
def originalComplementFirstGraph : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  (originalValueFirstGraph planarInclusionMap).comp
    (originalTangentialFirstGraph.comp (originalValueFirstGraph planarPartMap)) +
  (originalValueFirstGraph toroidalInclusionMap).comp
    ((startupCharacterFirstGraph 1 0).comp (originalValueFirstGraph toroidalPartMap))

def originalCircleFirstGraph : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ContinuousLinearMap.id ℂ _ - originalComplementFirstGraph

def originalPlanarMeanFreeFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  ContinuousLinearMap.id ℂ _ - originalAverageFirstGraph

def originalScalarMeanFreeFirstGraph : StartupFirst 1 →L[ℂ] StartupFirst 1 :=
  ContinuousLinearMap.id ℂ _ - startupCharacterFirstGraph 1 0

/-- Z1=(R-J)^{-1}(I-A), using precisely the opposite helicity shifts
 established in AKY2; no small angular modes are compressed. -/
def originalCovariantInverseFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  (startupTrueAngularFirstGraph 2 (-1)).comp (originalValueFirstGraph positiveHelicity) +
    (startupTrueAngularFirstGraph 2 1).comp (originalValueFirstGraph negativeHelicity)

def originalScalarInverseFirstGraph : StartupFirst 1 →L[ℂ] StartupFirst 1 :=
  startupTrueAngularFirstGraph 1 0

def originalGradientRecoveryFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  originalPlanarMeanFreeFirstGraph +
    (2 : ℂ) • (originalCovariantInverseFirstGraph.comp (originalValueFirstGraph quarterValueMap))


theorem originalValueFirstGraph_compatible {input output : ℕ} (mapping : OperatorValue input output) :
    StartupCompatible (originalValueKernel mapping) (originalValueFirstGraph mapping) :=
  startupPointFirstGraph_compatible _ _

theorem originalAverageFirstGraph_compatible : StartupCompatible originalAverageKernel originalAverageFirstGraph :=
  startupCompatible_add
    (startupCompatible_comp (originalValueFirstGraph_compatible _) (startupCharacterFirstGraph_compatible _ _))
    (startupCompatible_comp (originalValueFirstGraph_compatible _) (startupCharacterFirstGraph_compatible _ _))

theorem originalTangentialFirstGraph_compatible : StartupCompatible originalTangentialKernel originalTangentialFirstGraph :=
  startupCompatible_smul _ (startupCompatible_comp
    (startupCompatible_sub (startupCompatible_id _) (startupPointFirstGraph_compatible _ _))
    originalAverageFirstGraph_compatible)

theorem originalComplementFirstGraph_compatible : StartupCompatible originalComplementKernel originalComplementFirstGraph :=
  startupCompatible_add
    (startupCompatible_comp (originalValueFirstGraph_compatible _)
      (startupCompatible_comp originalTangentialFirstGraph_compatible (originalValueFirstGraph_compatible _)))
    (startupCompatible_comp (originalValueFirstGraph_compatible _)
      (startupCompatible_comp (startupCharacterFirstGraph_compatible _ _) (originalValueFirstGraph_compatible _)))

theorem originalCircleFirstGraph_compatible : StartupCompatible originalCircleKernel originalCircleFirstGraph :=
  startupCompatible_sub (startupCompatible_id _) originalComplementFirstGraph_compatible

theorem originalPlanarMeanFreeFirstGraph_compatible : StartupCompatible originalPlanarMeanFreeKernel originalPlanarMeanFreeFirstGraph :=
  startupCompatible_sub (startupCompatible_id _) originalAverageFirstGraph_compatible

theorem originalScalarMeanFreeFirstGraph_compatible : StartupCompatible originalScalarMeanFreeKernel originalScalarMeanFreeFirstGraph :=
  startupCompatible_sub (startupCompatible_id _) (startupCharacterFirstGraph_compatible _ _)

theorem originalCovariantInverseFirstGraph_compatible : StartupCompatible originalCovariantInverseKernel originalCovariantInverseFirstGraph :=
  startupCompatible_add
    (startupCompatible_comp (startupTrueAngularFirstGraph_compatible _ _) (originalValueFirstGraph_compatible _))
    (startupCompatible_comp (startupTrueAngularFirstGraph_compatible _ _) (originalValueFirstGraph_compatible _))

theorem originalScalarInverseFirstGraph_compatible : StartupCompatible originalScalarInverseKernel originalScalarInverseFirstGraph :=
  startupTrueAngularFirstGraph_compatible _ _

theorem originalGradientRecoveryFirstGraph_compatible : StartupCompatible originalGradientRecoveryKernel originalGradientRecoveryFirstGraph :=
  startupCompatible_add originalPlanarMeanFreeFirstGraph_compatible
    (startupCompatible_smul _ (startupCompatible_comp originalCovariantInverseFirstGraph_compatible (originalValueFirstGraph_compatible _)))

end Grad.CartesianStartup
