import AEE6ActualSingleModeGraphCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowSmoothGraph (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    (LowAnnularIndex →₀ SmoothRadialCore 1) →ₗ[ℝ] lowEnergyGraph lower length positive :=
  (lowFiniteSmoothCore lower length positive bounded).codRestrict
    ((lowEnergyGraph lower length positive).restrictScalars ℝ)
    (lowFiniteSmoothCore_mem lower length positive bounded)

theorem lowSmoothGraph_value (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowEnergyValue lower positive index (lowSmoothGraph lower length positive bounded core).val =
      smoothRadialValueL2 1 lower (core index) := by
  classical
  change lowEnergyValue lower positive index (lowFiniteSmoothCore lower length positive bounded core) = _
  rw [lowFiniteSmoothCore, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ other ∈ core.support,
    lowEnergyValue lower positive index
      (lowSingleRadialGraph lower length positive bounded other (weightedRadialCoreInto 1 lower (core other))).val) = _
  simp_rw [lowSingleRadialGraph_value, weightedToOrdinary_core, collarH1Coordinate_core_zero]
  by_cases member : index ∈ core.support
  · simp [member, smoothRadialValueL2]
  · have zero : core index = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
    simp [member, zero, smoothRadialValueL2]

theorem lowSmoothGraph_derivative (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowEnergyDerivative lower length positive index (lowSmoothGraph lower length positive bounded core).val =
      collarContinuousL2 (ComplexEuclidean 1) lower (core index).val.val.2 := by
  classical
  change lowEnergyDerivative lower length positive index (lowFiniteSmoothCore lower length positive bounded core) = _
  rw [lowFiniteSmoothCore, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ other ∈ core.support,
    lowEnergyDerivative lower length positive index
      (lowSingleRadialGraph lower length positive bounded other (weightedRadialCoreInto 1 lower (core other))).val) = _
  simp_rw [lowSingleRadialGraph_derivative, weightedToOrdinary_core, collarH1Coordinate_core_one]
  by_cases member : index ∈ core.support
  · simp [member]
  · have zero : core index = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
    simp [member, zero]

theorem lowSmoothGraph_section (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowEnergySection lower length positive bounded (lowSmoothGraph lower length positive bounded core) index =
      smoothRadialSection 1 lower (core index) := by
  apply radialSectionL2_injective lower positive bounded
  rw [lowEnergySection_bulk, lowSmoothGraph_value, radialSectionL2_core]

theorem lowSmoothGraph_incoming (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowIncomingTrace lower length positive bounded (lowSmoothGraph lower length positive bounded core) index =
      (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) •
        (core index).val.val.1 lower := by
  rw [lowIncomingTrace_apply]
  unfold lowEnergyEndpoint
  rw [lowSmoothGraph_section]
  rfl

end Grad.AnnularLowCompletion
