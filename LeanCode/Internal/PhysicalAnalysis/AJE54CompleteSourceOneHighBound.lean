import AJE49ActualStrongGeneratorCoordinates
import AJE53SourceFrequencyAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularInverseCalculus
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

section Observation
variable {H ι V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

theorem observedSource_augmented_oneHigh (parameters : PhaseParameters) (base : ACore parameters 3)
    (rho epsilon : ℝ) (projection : H →L[ℝ] lp (fun _ : ι => V) 2)
    (projectionBound : ∀ data, ‖projection data‖ ≤ ‖data‖)
    (frequency : ι → ℝ) (mode : ι → ℤ) (oneLe : ∀ index, 1 ≤ frequency index)
    (modeBound : ∀ index, |(mode index : ℝ)| ≤ frequency index)
    (data weighted generator : H) (grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1)
    (weightedActual : ∀ index, projection weighted index = frequency index ^ grade • projection data index)
    (generatorActual : ∀ index, projection generator index = (Complex.I * (mode index : ℂ)) ^ (grade - order) • projection data index) :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) * ‖projection generator‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  have allocated := sourceLp_augmented_oneHigh parameters base rho epsilon frequency mode oneLe modeBound
    (projection data) (projection weighted) (projection generator) grade order gradePositive ordered small weightedActual generatorActual
  exact allocated.trans (mul_le_mul_of_nonneg_left
    (add_le_add (projectionBound weighted) (mul_le_mul_of_nonneg_left (projectionBound data)
      (physicalBudget_nonnegative _ _ _ _ _)))
    (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le 8 grade))))
end Observation

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (data weighted : StrongDataCarrier parameters lower positive bounded 0 0)
    (support : StrongCutSupport) (finite : StrongSupported parameters lower positive bounded support data)
    (axis : Bool) (grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1)
    (actual : StrongInsertedGrade parameters lower positive bounded grade data weighted)

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_Known (slot : Fin 4) :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongKnownObservation parameters lower positive bounded slot
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongKnownObservation parameters lower positive bounded slot)
    (strongKnownObservation_bound parameters lower positive bounded slot)
    (fun index : (ℤ × ℤ) => Grad.AnnularVariational.annularFrequency index.1 index.2)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact actual.1 slot index
  · exact strongAxisGenerator_Known parameters lower positive bounded data support finite axis (grade - order) slot

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_Auxiliary (slot : Fin 3) :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongAuxiliaryObservation parameters lower positive bounded slot
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongAuxiliaryObservation parameters lower positive bounded slot)
    (strongAuxiliaryObservation_bound parameters lower positive bounded slot)
    (fun index : (ℤ × ℤ) => Grad.AnnularVariational.annularFrequency index.1 index.2)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact actual.2.1 slot index
  · exact strongAxisGenerator_Auxiliary parameters lower positive bounded data support finite axis (grade - order) slot

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_F0  :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongF0Observation parameters lower positive bounded 
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongF0Observation parameters lower positive bounded )
    (strongF0Observation_bound parameters lower positive bounded )
    (fun index : (ℤ × ℤ) => Grad.AnnularVariational.annularFrequency index.1 index.2)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact congrArg (fun field : WeightedRadialH1 1 lower => field.val) (actual.2.2.1 index)
  · exact strongAxisGenerator_F0 parameters lower positive bounded data support finite axis (grade - order) 

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_F2  :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongF2Observation parameters lower positive bounded 
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongF2Observation parameters lower positive bounded )
    (strongF2Observation_bound parameters lower positive bounded )
    (fun index : (ℤ × ℤ) => Grad.AnnularVariational.annularFrequency index.1 index.2)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact congrArg (fun field : WeightedRadialH1 1 lower => field.val) (actual.2.2.2.1 index)
  · exact strongAxisGenerator_F2 parameters lower positive bounded data support finite axis (grade - order) 

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_Outer  :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongOuterObservation parameters lower positive bounded 
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongOuterObservation parameters lower positive bounded )
    (strongOuterObservation_bound parameters lower positive bounded )
    (fun index : (ℤ × ℤ) => Grad.AnnularVariational.annularFrequency index.1 index.2)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact actual.2.2.2.2.1 index
  · exact strongAxisGenerator_Outer parameters lower positive bounded data support finite axis (grade - order) 

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_HighIncoming  :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongHighIncomingObservation parameters lower positive bounded 
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongHighIncomingObservation parameters lower positive bounded )
    (strongHighIncomingObservation_bound parameters lower positive bounded )
    (fun index : HighAnnularMode => Grad.AnnularVariational.annularFrequency index.val.1 index.val.2)
    (fun index : HighAnnularMode => sourceAxisFrequency axis index.val)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index.val) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact actual.2.2.2.2.2.1 index
  · exact strongAxisGenerator_HighIncoming parameters lower positive bounded data support finite axis (grade - order) 

include support finite actual gradePositive ordered small in
theorem strongSourceOneHigh_LowIncoming  :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongLowIncomingObservation parameters lower positive bounded 
        (strongAxisGenerator parameters lower positive bounded data axis (grade - order))‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  apply observedSource_augmented_oneHigh parameters base rho epsilon
    (strongLowIncomingObservation parameters lower positive bounded )
    (strongLowIncomingObservation_bound parameters lower positive bounded )
    (fun index : LowAnnularIndex => Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2)
    (fun index : LowAnnularIndex => sourceAxisFrequency axis index.2.val)
    (fun index => annularFrequency_one_le _ _)
    (fun index => sourceAxisFrequency_bound axis index.2.val) data weighted
    (strongAxisGenerator parameters lower positive bounded data axis (grade - order)) grade order gradePositive ordered small
  · intro index
    exact actual.2.2.2.2.2.2 index
  · exact strongAxisGenerator_LowIncoming parameters lower positive bounded data support finite axis (grade - order) 

include support finite actual gradePositive ordered small in
/-- Original full shared source one-high estimate. The constant depends on
order only; the original analytic width, rho powers and B8 ball are unchanged. -/
theorem strongAxisGenerator_augmented_oneHigh :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) *
      ‖strongAxisGenerator parameters lower positive bounded data axis (grade - order)‖ ≤
      (11 * (1 + physicalInterpolationConstant 8 grade)) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖data‖) := by
  let generator := strongAxisGenerator parameters lower positive bounded data axis (grade - order)
  have totalBound := StrongDataCarrier.norm_le_sum parameters lower positive bounded 0 0 generator
  have observedTotal : ‖generator‖ ≤
      ‖strongKnownObservation parameters lower positive bounded 0 generator‖ +
      ‖strongKnownObservation parameters lower positive bounded 1 generator‖ +
      ‖strongKnownObservation parameters lower positive bounded 2 generator‖ +
      ‖strongKnownObservation parameters lower positive bounded 3 generator‖ +
      ‖strongAuxiliaryObservation parameters lower positive bounded 0 generator‖ +
      ‖strongAuxiliaryObservation parameters lower positive bounded 1 generator‖ +
      ‖strongF0Observation parameters lower positive bounded  generator‖ +
      ‖strongF2Observation parameters lower positive bounded  generator‖ +
      ‖strongOuterObservation parameters lower positive bounded  generator‖ +
      ‖strongHighIncomingObservation parameters lower positive bounded  generator‖ +
      ‖strongLowIncomingObservation parameters lower positive bounded  generator‖ := by
    simpa only [strongKnownObservation_apply,strongAuxiliaryObservation_apply,strongF0Observation_apply,
      strongF2Observation_apply,strongOuterObservation_apply,strongHighIncomingObservation_apply,
      strongLowIncomingObservation_apply,sourceGraphLpAmbient_norm,Submodule.norm_coe] using totalBound
  exact elevenSourceBounds _ _ _ _
    ‖strongKnownObservation parameters lower positive bounded 0 generator‖
    ‖strongKnownObservation parameters lower positive bounded 1 generator‖
    ‖strongKnownObservation parameters lower positive bounded 2 generator‖
    ‖strongKnownObservation parameters lower positive bounded 3 generator‖
    ‖strongAuxiliaryObservation parameters lower positive bounded 0 generator‖
    ‖strongAuxiliaryObservation parameters lower positive bounded 1 generator‖
    ‖strongF0Observation parameters lower positive bounded  generator‖
    ‖strongF2Observation parameters lower positive bounded  generator‖
    ‖strongOuterObservation parameters lower positive bounded  generator‖
    ‖strongHighIncomingObservation parameters lower positive bounded  generator‖
    ‖strongLowIncomingObservation parameters lower positive bounded  generator‖
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) observedTotal
    (strongSourceOneHigh_Known parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 0)
    (strongSourceOneHigh_Known parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 1)
    (strongSourceOneHigh_Known parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 2)
    (strongSourceOneHigh_Known parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 3)
    (strongSourceOneHigh_Auxiliary parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 0)
    (strongSourceOneHigh_Auxiliary parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual 1)
    (strongSourceOneHigh_F0 parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual )
    (strongSourceOneHigh_F2 parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual )
    (strongSourceOneHigh_Outer parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual )
    (strongSourceOneHigh_HighIncoming parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual )
    (strongSourceOneHigh_LowIncoming parameters lower positive bounded base rho epsilon data weighted support finite axis grade order gradePositive ordered small actual )

end Grad.AnnularStrongOrbit
