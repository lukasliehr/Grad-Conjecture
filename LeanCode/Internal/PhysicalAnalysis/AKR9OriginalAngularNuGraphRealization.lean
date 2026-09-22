import AKR8ExactHighEnergyTupleCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularVariational Grad.CircularHighRegularity
open Grad.AnnularCurrentSource Grad.AnnularCurrentGreen Grad.AnnularOriginalHigh Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

/-- Actual angular derivative of either radial jet. The extra angular
source grade makes this a full square-summable bulk row. -/
def tupleAngularJetBulk (coordinate : Fin 2) : DivisionRow 1 lower :=
  sourceAngularBulk lower (annularSourceCoordinate parameters 1 lower 1 0 coordinate
    (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 1 0))

theorem tupleAngularJetBulk_mode (coordinate : Fin 2) (mode : ℤ × ℤ) :
    tupleAngularJetBulk parameters lower positive bounded tuple slot coordinate mode =
      (Complex.I * (mode.1 : ℂ)) • radialSqrtMap 1 lower
        (tupleConjugatedJetL2 parameters lower positive bounded tuple slot coordinate.val mode) := by
  change sourceAngularRatio mode • weightedRadialCoordinate 1 lower coordinate
    (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 1 0 mode) = _
  rw [tupleOriginalSourceGraph_stored]
  change sourceAngularRatio mode • ((splitTangentialWeight 1 0 mode : ℂ) •
    radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot coordinate.val mode)) = _
  rw [← mul_smul]
  have scalar : sourceAngularRatio mode * (splitTangentialWeight 1 0 mode : ℂ) = Complex.I * (mode.1 : ℂ) := by
    simp only [sourceAngularRatio,splitTangentialWeight,pow_one,pow_zero,mul_one]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity : (1 + |(mode.1 : ℝ)| : ℝ) ≠ 0))
  rw [scalar]

def originalHighNuReserve (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularSymbolFamily lower (fun mode => frequencyReserveSymbol 1 mode.val) 1 zero_le_one
    (fun mode => frequencyReserveSymbol_bound 1 mode.val)

def tupleOriginalNuAmbient : AnnularOmegaAmbient lower := WithLp.toLp 2
  ![highFullRestriction lower (tupleAngularJetBulk parameters lower positive bounded tuple slot 0),
    originalHighNuReserve lower (highFullRestriction lower (tupleAngularJetBulk parameters lower positive bounded tuple slot 1))]

/-- The original nu-normalized slope is the genuine derivative of the
SAME angular derivative field, not an independent graph coordinate. -/
theorem tupleOriginalNuAmbient_mem :
    tupleOriginalNuAmbient parameters lower positive bounded tuple slot ∈ originalNuGraph lower positive := by
  rw [originalNuGraph_mem_iff]
  intro mode
  change CollarWeakDerivative lower
    (radialOrdinary 1 lower positive (tupleAngularJetBulk parameters lower positive bounded tuple slot 0 mode.val))
    (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 •
      radialOrdinary 1 lower positive (frequencyReserveSymbol 1 mode.val •
        tupleAngularJetBulk parameters lower positive bounded tuple slot 1 mode.val))
  rw [tupleAngularJetBulk_mode,tupleAngularJetBulk_mode,map_smul,map_smul,map_smul,
    radialOrdinary_sqrt,radialOrdinary_sqrt]
  have inverse : (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) *
      frequencyReserveSymbol 1 mode.val = 1 := by
    change (Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 : ℂ) *
      ((Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 : ℂ)^1)⁻¹ = 1
    rw [pow_one,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode.val).ne')]
  change CollarWeakDerivative lower ((Complex.I * (mode.val.1 : ℂ)) •
    tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode.val)
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) •
      (frequencyReserveSymbol 1 mode.val • ((Complex.I * (mode.val.1 : ℂ)) •
        tupleConjugatedJetL2 parameters lower positive bounded tuple slot 1 mode.val)))
  rw [← mul_smul, inverse,one_smul]
  exact collarWeakDerivative_complex_smul lower _ _ _
    (tupleConjugatedJet_weak parameters lower positive bounded tuple slot 0 mode.val)

def tupleOriginalNu : originalNuGraph lower positive :=
  ⟨tupleOriginalNuAmbient parameters lower positive bounded tuple slot,
    tupleOriginalNuAmbient_mem parameters lower positive bounded tuple slot⟩

end Grad.AnnularOriginalCoreRealization
