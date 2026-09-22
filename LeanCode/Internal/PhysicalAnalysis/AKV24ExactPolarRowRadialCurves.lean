import AKV23ActualKappaWeightedRadialSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.SourceBoundaryTrace Grad.PhaseAlgebra
open Grad.Constraints.Gauges

theorem weightedAngularHilbertShift_weighted {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (shift : ℤ) (input : CellL2 dimension) (physical : (ℤ × ℤ) → ComplexEuclidean dimension)
    (same : ∀ mode, input mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • physical mode)
    (mode : ℤ × ℤ) :
    weightedAngularHilbertShift parameters dimension grade shift input mode =
      (annularFrequency mode.1 mode.2 : ℂ)^grade • physical (mode.1-shift, mode.2) := by
  rw [weightedAngularHilbertShift_apply,same,smul_smul,annularShiftScalar_weight]

theorem weightedHilbertRadial_weighted (parameters : PhaseParameters) (grade : ℕ)
    (input : CellL2 2) (physical : (ℤ × ℤ) → ComplexEuclidean 2)
    (same : ∀ mode, input mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • physical mode)
    (mode : ℤ × ℤ) :
    weightedHilbertRadial parameters grade input mode =
      (annularFrequency mode.1 mode.2 : ℂ)^grade •
        (planarComponentMap 0 ((2 : ℂ)⁻¹ • (physical (mode.1-1,mode.2)+physical (mode.1+1,mode.2))) +
         planarComponentMap 1 ((2*Complex.I : ℂ)⁻¹ • (physical (mode.1-1,mode.2)-physical (mode.1+1,mode.2)))) := by
  change planarComponentMap 0 ((2 : ℂ)⁻¹ •
    (weightedAngularHilbertShift parameters 2 grade 1 input mode + weightedAngularHilbertShift parameters 2 grade (-1) input mode)) +
    planarComponentMap 1 ((2*Complex.I : ℂ)⁻¹ •
    (weightedAngularHilbertShift parameters 2 grade 1 input mode - weightedAngularHilbertShift parameters 2 grade (-1) input mode)) = _
  rw [weightedAngularHilbertShift_weighted parameters grade 1 input physical same mode,
    weightedAngularHilbertShift_weighted parameters grade (-1) input physical same mode]
  apply PiLp.ext
  intro component
  fin_cases component
  simp [planarComponentMap,smul_smul]
  ring

theorem weightedHilbertTangential_weighted (parameters : PhaseParameters) (grade : ℕ)
    (input : CellL2 2) (physical : (ℤ × ℤ) → ComplexEuclidean 2)
    (same : ∀ mode, input mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • physical mode)
    (mode : ℤ × ℤ) :
    weightedHilbertTangential parameters grade input mode =
      (annularFrequency mode.1 mode.2 : ℂ)^grade •
        (planarComponentMap 1 ((2 : ℂ)⁻¹ • (physical (mode.1-1,mode.2)+physical (mode.1+1,mode.2))) -
         planarComponentMap 0 ((2*Complex.I : ℂ)⁻¹ • (physical (mode.1-1,mode.2)-physical (mode.1+1,mode.2)))) := by
  change planarComponentMap 1 ((2 : ℂ)⁻¹ •
    (weightedAngularHilbertShift parameters 2 grade 1 input mode + weightedAngularHilbertShift parameters 2 grade (-1) input mode)) -
    planarComponentMap 0 ((2*Complex.I : ℂ)⁻¹ •
    (weightedAngularHilbertShift parameters 2 grade 1 input mode - weightedAngularHilbertShift parameters 2 grade (-1) input mode)) = _
  rw [weightedAngularHilbertShift_weighted parameters grade 1 input physical same mode,
    weightedAngularHilbertShift_weighted parameters grade (-1) input physical same mode]
  apply PiLp.ext
  intro component
  fin_cases component
  simp [planarComponentMap,smul_smul]
  ring

def OriginalRowRadialCurves.radial {parameters : PhaseParameters} {lower : ℝ}
    {row : DivisionRow 2 lower} (curves : OriginalRowRadialCurves parameters lower row) (positive : 0 < lower) :
    OriginalRowRadialCurves parameters lower (radialRowContraction lower positive 0 row) where
  curve grade radius := weightedHilbertRadial parameters grade (curves.curve grade radius)
  smooth grade := (weightedHilbertRadial parameters grade).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,radialRowContraction_decoded_ae parameters lower positive row] with radius same contracted
    intro mode
    rw [weightedHilbertRadial_weighted parameters grade _ _ same mode,contracted mode]
    apply PiLp.ext
    intro component
    fin_cases component
    simp [planarComponentMap,smul_smul]
    ring

def OriginalRowRadialCurves.tangential {parameters : PhaseParameters} {lower : ℝ}
    {row : DivisionRow 2 lower} (curves : OriginalRowRadialCurves parameters lower row) (positive : 0 < lower) :
    OriginalRowRadialCurves parameters lower (tangentialRowContraction lower positive 0 row) where
  curve grade radius := weightedHilbertTangential parameters grade (curves.curve grade radius)
  smooth grade := (weightedHilbertTangential parameters grade).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,tangentialRowContraction_decoded_ae parameters lower positive row] with radius same contracted
    intro mode
    rw [weightedHilbertTangential_weighted parameters grade _ _ same mode,contracted mode]
    apply PiLp.ext
    intro component
    fin_cases component
    simp [planarComponentMap,smul_smul]
    ring

end Grad.AnnularGeneralSourceRegularity
