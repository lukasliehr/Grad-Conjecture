import AIW6UniformOriginalLowFactors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace

/-- Actual v component, obtained from the decoded weighted value w. -/
def lowEnergyToAJComponentValue (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    lowEnergyGraph lower length positive →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarScalar 1 lower (originalLowRatio parameters lower length positive index)).comp
    ((lowEnergyValue lower positive index).comp (lowEnergyGraph lower length positive).subtypeL)

/-- Actual Lambda^-1 v'. The second term uses ADY's decoded w', including
its genuine rho storage correction, not the derivative of the stored value. -/
def lowEnergyToAJComponentSlope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    lowEnergyGraph lower length positive →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (cellFrequency index.2.val.2)⁻¹ •
    (((collarScalar 1 lower (originalLowRatioSlope parameters lower length positive index)).comp
      ((lowEnergyValue lower positive index).comp (lowEnergyGraph lower length positive).subtypeL)) +
    ((collarScalar 1 lower (originalLowRatio parameters lower length positive index)).comp
      ((lowEnergyDerivative lower length positive index).comp (lowEnergyGraph lower length positive).subtypeL)))

theorem lowEnergyToAJComponent_weak (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex)
    (field : lowEnergyGraph lower length positive) :
    CollarWeakDerivative lower (lowEnergyToAJComponentValue parameters lower length positive index field)
      (cellFrequency index.2.val.2 • lowEnergyToAJComponentSlope parameters lower length positive index field) := by
  change CollarWeakDerivative lower
    (collarScalar 1 lower (originalLowRatio parameters lower length positive index)
      (lowEnergyValue lower positive index field.val))
    (cellFrequency index.2.val.2 • ((cellFrequency index.2.val.2)⁻¹ •
      (collarScalar 1 lower (originalLowRatioSlope parameters lower length positive index)
        (lowEnergyValue lower positive index field.val) +
       collarScalar 1 lower (originalLowRatio parameters lower length positive index)
        (lowEnergyDerivative lower length positive index field.val))))
  rw [smul_smul, mul_inv_cancel₀ (cellFrequency_pos index.2.val.2).ne', one_smul]
  exact (originalLowRatio_weak_iff parameters lower length positive lengthPositive index _ _).mpr (field.property index)

/-- The original AJ6 physical factor e^Phi S_ell (Lambda xi,x). -/
def originalLowAJPhysicalFactor (parameters : PhaseParameters) (lower length radius : ℝ)
    (index : LowAnnularIndex) : ℝ :=
  Real.exp (radialPhase parameters radius index.2.val.2) *
    if index.1 = 0 then originalLowScale parameters lower length index.2 * cellFrequency index.2.val.2 else 1

theorem originalLowAJ_factor_identity (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    originalLowRatio parameters lower length positive index radius * lowPhysicalFactor parameters length radius index =
      originalLowAJPhysicalFactor parameters lower length radius index := by
  have mu := (lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)).ne'
  have amplitude := (lowAmplitude_pos length parameters.gamma index.2).ne'
  unfold originalLowRatio lowPhysicalFactor originalLowAJPhysicalFactor
  split_ifs
  · change (originalLowScale parameters lower length index.2 / lowAmplitude length parameters.gamma index.2 *
      cellFrequency index.2.val.2 / originalLowSmoothMu lower length positive index.2.val.2 radius) *
      (Real.exp (radialPhase parameters radius index.2.val.2) *
        (lowAmplitude length parameters.gamma index.2 * lowMu length radius index.2.val.2)) = _
    rw [originalLowSmoothMu_physical lower length positive index.2.val.2 radius inside]
    field_simp
  · change 1 * (Real.exp (radialPhase parameters radius index.2.val.2) * 1) = _
    ring

def originalLowAJSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (originalLowRatio parameters lower length positive index)
    (lowEnergySection lower length positive bounded field index)

/-- The SAME physical xi,x of ADY is carried into the ORIGINAL AJ scaling. -/
theorem originalLowAJSection_physical (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    originalLowAJSection parameters lower length positive bounded field index radius =
      originalLowAJPhysicalFactor parameters lower length radius.val index •
        lowPhysicalSection parameters lower length positive bounded field index radius := by
  change originalLowRatio parameters lower length positive index radius.val •
    lowEnergySection lower length positive bounded field index radius = _
  rw [← lowPhysicalSection_encode parameters lower length positive bounded field index radius,
    smul_smul, originalLowAJ_factor_identity parameters lower length positive index radius.val radius.property]

end Grad.AnnularOriginalLow
