import AAQ3NormalizedRadialMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev AnnularFluxAmbient (lower length : ℝ) (positive : 0 < lower) :=
  annularEnergySpace lower length positive × AnnularForcing lower

def annularFluxState (lower length : ℝ) (positive : 0 < lower) :
    AnnularFluxAmbient lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  ContinuousLinearMap.fst ℂ _ _

def annularFluxSource (lower length : ℝ) (positive : 0 < lower) :
    AnnularFluxAmbient lower length positive →L[ℂ] AnnularForcing lower := ContinuousLinearMap.snd ℂ _ _

def annularFluxF (lower length : ℝ) (positive : 0 < lower) :
    AnnularFluxAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (ContinuousLinearMap.fst ℂ _ _).comp (annularFluxSource lower length positive)

def annularFluxG (lower length : ℝ) (positive : 0 < lower) :
    AnnularFluxAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (annularFluxSource lower length positive))

def annularFluxF2 (lower length : ℝ) (positive : 0 < lower) :
    AnnularFluxAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (ContinuousLinearMap.fst ℂ _ _).comp ((ContinuousLinearMap.snd ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (annularFluxSource lower length positive)))

section NormalizedSlope
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularFluxQ : AnnularFluxAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength +
    annularEnergyRadial lower length positive).comp (annularFluxState lower length positive) -
      annularFluxF lower length positive

theorem annularFluxQ_apply (data : AnnularFluxAmbient lower length positive) :
    annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data =
      annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength data.1 data.2.1 := rfl

def annularFluxPhase : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun mode => annularFrequencyCurve mode (annularPhaseCurve parameters mode.val.2))
    (annularFluxPotentialConstant lower length) (annularFluxPotentialConstant_nonnegative lower length)
    (annularNormalizedPhase_bound parameters lower length positive lengthPositive widthHalf widthLength)

def annularFluxInverseRadius : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun mode => annularFrequencyCurve mode (annularInverseRadiusCurve lower positive))
    lower⁻¹ (inv_nonneg.mpr positive.le) (annularNormalizedInverseRadius_bound lower positive)

def annularFluxInverseSquare : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun mode => annularFrequencyCurve mode (annularInverseSquareCurve lower positive))
    (4 * lower⁻¹ ^ 2) (by positivity) (annularNormalizedInverseSquare_bound lower positive)

def annularFluxD : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularSymbolFamily lower (fun mode => ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) •
    annularDSymbol mode) 1 (by norm_num) annularNormalizedD_bound

def annularFluxCell : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularSymbolFamily lower (fun mode => ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) •
    annularCellSymbol length mode) length⁻¹ (inv_nonneg.mpr lengthPositive.le)
    (annularNormalizedCell_bound length lengthPositive)

/-- The actual sqrt(r) nu^-1 derivative of e^Phi q, expressed using only
undifferentiated source coordinates and the energy state. -/
def annularFluxSlope : AnnularFluxAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (annularFluxPhase parameters lower length positive lengthPositive widthHalf widthLength +
      annularFluxInverseRadius lower positive).comp
    (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength) +
  (annularNormalizedPotentialMap lower length positive).comp (annularFluxState lower length positive) -
  (annularFluxInverseSquare lower positive).comp
    ((annularEnergyValue lower length positive).comp (annularFluxState lower length positive)) -
  (annularFluxD lower).comp (annularFluxG lower length positive) -
  (annularFluxCell lower length lengthPositive).comp (annularFluxF2 lower length positive)

theorem annularFluxSlope_ordinary (bounded : lower ≤ 1)
    (data : AnnularFluxAmbient lower length positive) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive
      (annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength data mode) =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) •
        annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded data.1 data.2 mode := by
  let ν := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have phaseLaw := annularScalarFamily_ordinary lower positive
    (fun mode => annularFrequencyCurve mode (annularPhaseCurve parameters mode.val.2))
    (annularFluxPotentialConstant lower length) (annularFluxPotentialConstant_nonnegative lower length)
    (annularNormalizedPhase_bound parameters lower length positive lengthPositive widthHalf widthLength)
    (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode
  have radialLaw := annularScalarFamily_ordinary lower positive
    (fun mode => annularFrequencyCurve mode (annularInverseRadiusCurve lower positive))
    lower⁻¹ (inv_nonneg.mpr positive.le) (annularNormalizedInverseRadius_bound lower positive)
    (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode
  have inverseLaw := annularScalarFamily_ordinary lower positive
    (fun mode => annularFrequencyCurve mode (annularInverseSquareCurve lower positive))
    (4 * lower⁻¹ ^ 2) (by positivity) (annularNormalizedInverseSquare_bound lower positive)
    (annularEnergyValue lower length positive data.1) mode
  simp only [collarScalar_frequency] at phaseLaw radialLaw inverseLaw
  rw [annularEnergyValue_ordinary lower length positive bounded mode data.1, collarScalar_inverseSquare] at inverseLaw
  have potentialLaw := annularNormalizedPotentialMap_ordinary lower length positive bounded data.1 mode
  rw [annularNormalizedQSlope_formula]
  change radialOrdinary 1 lower positive
    (annularFluxPhase parameters lower length positive lengthPositive widthHalf widthLength
        (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode +
      annularFluxInverseRadius lower positive
        (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode +
      annularNormalizedPotentialMap lower length positive data.1 mode -
      annularFluxInverseSquare lower positive (annularEnergyValue lower length positive data.1) mode -
      ((ν⁻¹ : ℝ) • annularDSymbol mode) • data.2.2.1 mode -
      ((ν⁻¹ : ℝ) • annularCellSymbol length mode) • data.2.2.2.1 mode) = _
  simp only [map_add, map_sub, map_smul]
  change radialOrdinary 1 lower positive (annularFluxPhase parameters lower length positive lengthPositive widthHalf widthLength
    (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode) = _ at phaseLaw
  change radialOrdinary 1 lower positive (annularFluxInverseRadius lower positive
    (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data) mode) = _ at radialLaw
  change radialOrdinary 1 lower positive (annularFluxInverseSquare lower positive
    (annularEnergyValue lower length positive data.1) mode) = _ at inverseLaw
  have sumLaw := congrArg₂ (fun first second : CollarL2 (ComplexEuclidean 1) lower => first + second)
    (congrArg₂ (fun first second : CollarL2 (ComplexEuclidean 1) lower => first + second) phaseLaw radialLaw) potentialLaw
  have differenceLaw := congrArg₂ (fun first second : CollarL2 (ComplexEuclidean 1) lower => first - second) sumLaw inverseLaw
  have fullLaw := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower =>
    value - ((ν⁻¹ : ℝ) • annularDSymbol mode) • radialOrdinary 1 lower positive (data.2.2.1 mode) -
      ((ν⁻¹ : ℝ) • annularCellSymbol length mode) • radialOrdinary 1 lower positive (data.2.2.2.1 mode)) differenceLaw
  refine fullLaw.trans ?_
  simp only [ν, smul_add, smul_sub, annularFluxQ_apply, smul_assoc]

end NormalizedSlope
end Grad.AnnularFluxTrace
