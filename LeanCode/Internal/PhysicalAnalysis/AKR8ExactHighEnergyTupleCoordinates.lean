import AKR7FullHighEnergyTupleRealization
import AKR4LiteralCopiedSourceRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularVariational Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleHighEnergy_derivative (mode : HighAnnularMode) :
    annularEnergyDerivative lower length positive (tupleHighEnergy parameters lower positive bounded tuple slot length) mode =
      radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 1 mode.val) := by
  change weightedRadialCoordinate 1 lower 1
    (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val) = _
  exact tupleConjugatedRadialGraph_coordinate parameters lower positive bounded tuple slot mode.val 1

theorem tupleHighEnergy_value (mode : HighAnnularMode) :
    annularEnergyValue lower length positive (tupleHighEnergy parameters lower positive bounded tuple slot length) mode =
      radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val) := by
  change annularValueMassMap lower length positive mode
    (collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
      (weightedRadialCoordinate 1 lower 0 (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val))) = _
  rw [tupleConjugatedRadialGraph_coordinate]
  change annularValueMassMap lower length positive mode
    (collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
      (radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val))) =
        radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val)
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode)
      (collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val))),
    collarScalar_ae 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
      (radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val))]
    with radius inverse mass
  change annularValueMassMap lower length positive mode _ radius = _ at inverse
  rw [inverse,mass]
  change (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ •
    (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius • _) = _
  rw [smul_smul,inv_mul_cancel₀ (annularPotentialWeight_pos lower length positive mode radius).ne',one_smul]

theorem tupleHighEnergy_radialGraph (mode : HighAnnularMode) :
    annularModeRadialH1 lower length positive mode (tupleHighEnergy parameters lower positive bounded tuple slot length) =
      tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val := by
  apply weightedRadial_value_injective 1 lower positive bounded.le
  rw [annularModeRadialH1_value,tupleHighEnergy_value,tupleConjugatedRadialGraph_coordinate]
  rfl

/-- Both original energy endpoint coordinates are traces of the same tuple
radial H1 graph. -/
theorem tupleHighEnergy_outer (mode : HighAnnularMode) :
    annularEnergyOuter lower length positive (tupleHighEnergy parameters lower positive bounded tuple slot length) mode =
      (Real.sqrt 2 : ℂ) • weightedRadialTrace 1 lower positive bounded 1
        (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val) := by
  rw [annularEnergyOuter_eq_trace,tupleHighEnergy_radialGraph]

end Grad.AnnularOriginalCoreRealization
