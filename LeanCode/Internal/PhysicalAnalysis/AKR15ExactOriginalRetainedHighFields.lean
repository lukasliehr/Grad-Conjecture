import AKR14ExactTuplePhysicalSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighRadial Grad.AnnularHighTilt Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.AnnularVariational
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularTiltedReference Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower)

/-- The literal original retained graph of an arbitrary admissible tuple.
The Xi block retains the original b_m-normalized E_B norm. -/
def tupleOriginalRetained : OriginalCoupledSpace lower length positive := WithLp.toLp 2
  (WithLp.toLp 2 (bEnergyNormalize lower length positive
    (tupleHighEnergy parameters lower positive bounded tuple 1 length),
    tupleOriginalNu parameters lower positive bounded tuple 0),
   tupleOriginalAJ parameters lower length positive bounded tuple)

def tupleWeightedRetained (lengthPositive : 0 < length) : CoupledSpace lower length positive lengthPositive :=
  originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive
    (tupleOriginalRetained parameters lower length positive bounded tuple)

theorem tupleWeightedRetained_highXi_section (mode : HighAnnularMode) (lengthPositive : 0 < length) :
    rawHighXiSection parameters lower length positive bounded
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.1.ofLp.1 mode =
      tuplePhysicalSection parameters lower bounded tuple 1 mode.val := by
  apply radialSectionL2_faithful lower positive bounded
  rw [rawHighXiSection_bulk]
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive (annularEnergyValue lower length positive
      (bEnergyDecode lower length positive (highEnergyWeight lower length positive bounded.le
        (bEnergyNormalize lower length positive (tupleHighEnergy parameters lower positive bounded tuple 1 length)))) mode)) = _
  rw [originalHighTilt_bDecode,bEnergyDecode_normalize,highEnergyWeight_value]
  rw [rawHighDecode_weighted_sqrt parameters lower positive bounded _ mode _
    (tupleHighEnergy_value parameters lower length positive bounded tuple 1 mode)]
  exact (radialSectionL2_scalar lower positive bounded.le (annularInversePhase parameters mode.val.2)
    (tupleConjugatedJetSection parameters lower bounded tuple 1 0 mode.val)).symm

theorem tupleWeightedRetained_highX_section (mode : HighAnnularMode) (lengthPositive : 0 < length) :
    rawHighXSection parameters lower length positive bounded lengthPositive
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.1.ofLp.2 mode =
      (Complex.I * (mode.val.1 : ℂ)) • tuplePhysicalSection parameters lower bounded tuple 0 mode.val := by
  apply radialSectionL2_faithful lower positive bounded
  rw [rawHighXSection_bulk]
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive ((originalFluxTiltEquivalence lower length positive bounded.le lengthPositive
      (tupleOriginalNu parameters lower positive bounded tuple 0)).val 0 mode)) = _
  rw [originalFluxTilt_value]
  have stored : (tupleOriginalNu parameters lower positive bounded tuple 0).val 0 mode =
      radialSqrtMap 1 lower ((Complex.I * (mode.val.1 : ℂ)) •
        tupleConjugatedJetL2 parameters lower positive bounded tuple 0 0 mode.val) := by
    change tupleAngularJetBulk parameters lower positive bounded tuple 0 0 mode.val = _
    rw [tupleAngularJetBulk_mode,map_smul]
    rfl
  rw [rawHighDecode_weighted_sqrt parameters lower positive bounded _ mode _ stored,map_smul]
  rw [radialSectionL2_complex_smul,tuplePhysicalSection,radialSectionL2_scalar]
  rfl

theorem tupleWeightedRetained_highXi (mode : HighAnnularMode) (lengthPositive : 0 < length)
    (radius : Icc lower (1 : ℝ)) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode.val =
        originalPhysicalCoefficient (tuple.val 1) radius.val mode := by
  rw [sameCoupledXiCoefficient_high,tupleWeightedRetained_highXi_section,tuplePhysicalSection_value]

theorem tupleWeightedRetained_highX (mode : HighAnnularMode) (lengthPositive : 0 < length)
    (radius : Icc lower (1 : ℝ)) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode.val =
        (Complex.I * (mode.val.1 : ℂ)) • originalPhysicalCoefficient (tuple.val 0) radius.val mode := by
  rw [sameCoupledXCoefficient_high,tupleWeightedRetained_highX_section]
  change (Complex.I * (mode.val.1 : ℂ)) • tuplePhysicalSection parameters lower bounded tuple 0 mode.val radius = _
  rw [tuplePhysicalSection_value]

end Grad.AnnularOriginalCoreRealization
