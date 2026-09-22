import AKR27UniqueTotalOriginalCoreImage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularVariational
open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem rawHighXiSection_add (first second : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    rawHighXiSection parameters lower length positive bounded (first+second) mode =
      rawHighXiSection parameters lower length positive bounded first mode + rawHighXiSection parameters lower length positive bounded second mode := by
  apply radialSectionL2_faithful lower positive bounded
  rw [map_add,rawHighXiSection_bulk,rawHighXiSection_bulk,rawHighXiSection_bulk]
  simp only [map_add,lp.coeFn_add,Pi.add_apply]

theorem rawHighXiSection_smul (scalar : ℂ) (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    rawHighXiSection parameters lower length positive bounded (scalar • field) mode =
      scalar • rawHighXiSection parameters lower length positive bounded field mode := by
  apply radialSectionL2_faithful lower positive bounded
  rw [radialSectionL2_complex_smul,rawHighXiSection_bulk,rawHighXiSection_bulk]
  simp only [map_smul,lp.coeFn_smul,Pi.smul_apply]

theorem rawHighXSection_add (lengthPositive : 0 < length)
    (first second : annularOmegaGraph lower length positive lengthPositive) (mode : HighAnnularMode) :
    rawHighXSection parameters lower length positive bounded lengthPositive (first+second) mode =
      rawHighXSection parameters lower length positive bounded lengthPositive first mode +
        rawHighXSection parameters lower length positive bounded lengthPositive second mode := by
  apply radialSectionL2_faithful lower positive bounded
  rw [map_add,rawHighXSection_bulk,rawHighXSection_bulk,rawHighXSection_bulk]
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive (first.val 0 mode+second.val 0 mode)) = _
  rw [map_add,map_add]

theorem rawHighXSection_smul (lengthPositive : 0 < length) (scalar : ℂ)
    (field : annularOmegaGraph lower length positive lengthPositive) (mode : HighAnnularMode) :
    rawHighXSection parameters lower length positive bounded lengthPositive (scalar • field) mode =
      scalar • rawHighXSection parameters lower length positive bounded lengthPositive field mode := by
  apply radialSectionL2_faithful lower positive bounded
  rw [radialSectionL2_complex_smul,rawHighXSection_bulk,rawHighXSection_bulk]
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive (scalar • field.val 0 mode)) = _
  rw [map_smul,map_smul]

theorem lowPhysicalSection_add (first second : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowPhysicalSection parameters lower length positive bounded (first+second) index =
      lowPhysicalSection parameters lower length positive bounded first index +
        lowPhysicalSection parameters lower length positive bounded second index := by
  unfold lowPhysicalSection
  rw [lowEnergySection_add]
  apply ContinuousMap.ext
  intro radius
  exact smul_add _ _ _

theorem lowPhysicalSection_smul (scalar : ℂ) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowPhysicalSection parameters lower length positive bounded (scalar • field) index =
      scalar • lowPhysicalSection parameters lower length positive bounded field index := by
  unfold lowPhysicalSection
  rw [lowEnergySection_smul]
  apply ContinuousMap.ext
  intro radius
  change lowPhysicalInverseCurve parameters lower length positive index radius.val •
    (scalar • lowEnergySection lower length positive bounded field index radius) =
    scalar • (lowPhysicalInverseCurve parameters lower length positive index radius.val •
      lowEnergySection lower length positive bounded field index radius)
  exact smul_comm _ _ _

end Grad.AnnularOriginalCoreRealization
