import AJE56SmoothOriginalFiniteSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy
attribute [local instance] originalAmbientRealNormed
  knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < length) (data : OriginalStrongCarrier parameters lower 0 0)
    (support : StrongCutSupport) (finite : OriginalSourceSupported parameters lower support data)

include finite in
theorem originalToStrong_supported : StrongSupported parameters lower positive bounded support
    (originalToStrong parameters lower length positive bounded lengthPositive 0 0 data) := by
  have f0Zero (mode : ℤ × ℤ) (outside : mode ∉ support.1) :
      unweightedSourceF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1 mode = 0 := by
    change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0 (data.val.ofLp.1.ofLp.1.ofLp.1 mode) = 0
    rw [finite.1 mode outside,map_zero,smul_zero]
  have rf0Zero (mode : ℤ × ℤ) (outside : mode ∉ support.1) :
      unweightedSourceRF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1 mode = 0 := by
    change sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0 (data.val.ofLp.1.ofLp.1.ofLp.1 mode) = 0
    rw [finite.1 mode outside,map_zero,smul_zero]
  have f2Zero (mode : ℤ × ℤ) (outside : mode ∉ support.1) :
      unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2 mode = 0 := by
    change weightedRadialCoordinate 1 lower 0 (data.val.ofLp.1.ofLp.1.ofLp.2 mode) = 0
    rw [finite.2.1 mode outside,map_zero]
  refine ⟨?_,?_,finite.1,finite.2.1,finite.2.2.2.2.1,?_,?_⟩
  · intro slot mode outside
    fin_cases slot
    · exact divisionHighWeight_zero_mode lower positive bounded _ mode (f0Zero mode outside)
    · exact divisionHighWeight_zero_mode lower positive bounded _ mode (rf0Zero mode outside)
    · exact divisionHighWeight_zero_mode lower positive bounded _ mode (f2Zero mode outside)
    · exact divisionHighWeight_zero_mode lower positive bounded _ mode (finite.2.2.1 mode outside)
  · intro slot mode outside
    fin_cases slot
    · apply divisionHighWeight_zero_mode lower positive bounded
      change (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • data.val.ofLp.1.ofLp.2.ofLp.2 mode = 0
      rw [finite.2.2.2.1 mode outside,smul_zero]
    · apply divisionHighWeight_zero_mode lower positive bounded
      rw [sourceAngularBulk_mode,finite.2.2.2.1 mode outside,smul_zero]
    · rfl
  · intro mode outside
    change lower ^ (-9 / 4 : ℝ) • data.val.ofLp.2.ofLp.2.ofLp.1 mode = 0
    rw [finite.2.2.2.2.2.1 mode outside,smul_zero]
  · intro index outside
    change (originalLowIncomingWeight parameters lower length index : ℂ) • data.val.ofLp.2.ofLp.2.ofLp.2 index = 0
    rw [finite.2.2.2.2.2.2 index outside,smul_zero]

/-- Full shared smooth approximants are literally finite in every original
source, angular graph and independent incoming coordinate. -/
theorem strongSmoothDenseMap_supported (core : OriginalSmoothSourceCore parameters) :
    StrongSupported parameters lower positive bounded (originalSmoothSupport parameters core)
      ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core) := by
  have actual := originalToStrong_supported parameters lower length positive bounded lengthPositive
    (originalSmoothStrongData parameters lower positive bounded core) (originalSmoothSupport parameters core)
    (originalSmoothStrongData_supported parameters lower positive bounded core)
  exact (congrArg (StrongSupported parameters lower positive bounded (originalSmoothSupport parameters core))
    (strongSmoothDenseMap_actual parameters lower length positive bounded lengthPositive core)).mpr actual

end Grad.AnnularStrongOrbit
