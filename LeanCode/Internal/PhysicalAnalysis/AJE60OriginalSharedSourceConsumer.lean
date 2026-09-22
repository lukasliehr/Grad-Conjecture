import AJE24SharedKnownFunctionalBounds
import AJE25SharedLowForcingTower
import AJE54CompleteSourceOneHighBound
import AJE57SameReconstructedSmoothSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy Grad.AnnularInverseCalculus
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  originalAmbientRealNormed

private theorem contractedAllocation {E : Type*} [NormedAddCommGroup E]
    (cut : E → E) (bound : ∀ data, ‖cut data‖ ≤ ‖data‖) (constant high : ℝ)
    (constantNonnegative : 0 ≤ constant) (highNonnegative : 0 ≤ high) (data weighted : E) :
    constant * (‖cut weighted‖ + high * ‖cut data‖) ≤ constant * (‖weighted‖ + high * ‖data‖) :=
  mul_le_mul_of_nonneg_left (add_le_add (bound weighted) (mul_le_mul_of_nonneg_left (bound data) highNonnegative)) constantNonnegative

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

theorem strongDataCut_actualSmoothOrbit (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (support : StrongCutSupport) (axis : Bool) :
    ContDiff ℝ ∞ (fun time : ℝ => strongDataTranslation parameters lower positive bounded 0 0 (time • axisVector axis)
      (strongDataCut parameters lower positive bounded support data)) :=
  finiteStrongDataOrbit_contDiff parameters lower positive bounded
    (strongDataCut parameters lower positive bounded support data) support
    (strongDataCut_supported parameters lower positive bounded support data) axis

/-- Actual source cutoff consumer: no smooth-data premise is assumed. The
same cut retains the original insertion and gives the full one-high bound. -/
theorem strongDataCut_actualOneHigh (base : ACore parameters 3) (rho epsilon : ℝ)
    (data weighted : StrongDataCarrier parameters lower positive bounded 0 0) (support : StrongCutSupport)
    (axis : Bool) (grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1)
    (actual : StrongInsertedGrade parameters lower positive bounded grade data weighted) :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongAxisGenerator parameters lower positive bounded
        (strongDataCut parameters lower positive bounded support data) axis (grade - order)‖ ≤
      (11 * (1 + physicalInterpolationConstant 8 grade)) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  have result := strongAxisGenerator_augmented_oneHigh parameters lower positive bounded base rho epsilon
    (strongDataCut parameters lower positive bounded support data)
    (strongDataCut parameters lower positive bounded support weighted) support
    (strongDataCut_supported parameters lower positive bounded support data) axis grade order gradePositive ordered small
    (strongDataCut_inserted parameters lower positive bounded support grade data weighted actual)
  exact result.trans (contractedAllocation (strongDataCut parameters lower positive bounded support)
    (strongDataCut_bound parameters lower positive bounded support) _ _
    (mul_nonneg (by norm_num) (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le 8 grade))))
    (physicalBudget_nonnegative _ _ _ _ _) data weighted)

/-- Genuine all-radial smooth finite sources are dense in the SAME complete
original strong carrier, and their complete angular/cell orbits are smooth. -/
theorem strongSmoothDenseMap_actualConsumer (length : ℝ) (lengthPositive : 0 < length) :
    DenseRange (strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping ∧
    ∀ (core : OriginalSmoothSourceCore parameters) (axis : Bool),
      ContDiff ℝ ∞ (fun time : ℝ => strongDataTranslation parameters lower positive bounded 0 0 (time • axisVector axis)
        ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)) :=
  ⟨(strongSmoothDenseMap parameters lower length positive bounded lengthPositive).dense,
    fun core axis => finiteStrongDataOrbit_contDiff parameters lower positive bounded
      ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)
      (originalSmoothSupport parameters core)
      (strongSmoothDenseMap_supported parameters lower length positive bounded lengthPositive core) axis⟩

end Grad.AnnularStrongOrbit
