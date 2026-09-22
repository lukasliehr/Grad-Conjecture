import AKAC11CommonRhoTangentialCorrection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularPhysicalFourier Grad.AnnularKernelL2 Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.AnnularCurrentLow Grad.AnnularCurrentEnergy Grad.Constraints.Gauges
open Grad.AnnularGeneralSourceRegularity Grad.AnnularSmoothCore Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularCurrentSource Grad.BoundaryLift Grad.PhaseAlgebra

theorem lowRhoPhysicalCoefficient_bulkUnit {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (output : Fin target) (input : Fin source) (field : DivisionRow source lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (bulkMatrixUnit lower output input field) radius mode =
        matrixUnit output input (lowRhoPhysicalCoefficient parameters lower positive field radius mode) := by
  filter_upwards [bulkMatrixUnit_ae lower output input field] with radius actual
  intro mode
  unfold lowRhoPhysicalCoefficient
  rw [actual mode,map_smul,matrixUnit_apply]

def SmoothLowPhysicalRow.add {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {first second : DivisionRow dimension lower}
    (a : SmoothLowPhysicalRow parameters lower positive first) (b : SmoothLowPhysicalRow parameters lower positive second) :
    SmoothLowPhysicalRow parameters lower positive (first+second) where
  curve grade radius := a.curve grade radius+b.curve grade radius
  smooth grade := (a.smooth grade).add (b.smooth grade)
  same grade := by
    filter_upwards [a.same grade,b.same grade,lowRhoPhysicalCoefficient_add_ae parameters lower positive first second]
      with radius one two added
    intro mode
    change a.curve grade radius mode+b.curve grade radius mode = _
    rw [one mode,two mode,added mode,smul_add,smul_add]

def SmoothLowPhysicalRow.bulkUnit {source target : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow source lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (output : Fin target) (input : Fin source) :
    SmoothLowPhysicalRow parameters lower positive (bulkMatrixUnit lower output input row) where
  curve grade radius := coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit output input)
    (norm_nonneg _) (fun _ => le_rfl) (curves.curve grade radius)
  smooth grade := (coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit output input)
    (norm_nonneg _) (fun _ => le_rfl)).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,lowRhoPhysicalCoefficient_bulkUnit parameters lower positive output input row]
      with radius same projected
    intro mode
    change matrixUnit output input (curves.curve grade radius mode) = _
    rw [same mode,projected mode,map_smul,map_smul]

def SmoothLowPhysicalRow.meanFree {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (meanFreeRow lower row) where
  curve grade radius := hilbertMeanFree parameters (curves.curve grade radius)
  smooth grade := (hilbertMeanFree parameters).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,lowRhoPhysicalCoefficient_projection parameters lower positive row] with radius same projected
    intro mode
    change (if mode.1=0 then (0 : ℂ) else 1) • curves.curve grade radius mode = _
    rw [same mode,projected mode]
    by_cases zero : mode.1=0 <;> simp [zero]

def SmoothLowPhysicalRow.tangential {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 2 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (tangentialRowContraction lower positive 0 row) where
  curve grade radius := weightedHilbertTangential parameters grade (curves.curve grade radius)
  smooth grade := (weightedHilbertTangential parameters grade).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,lowRhoPhysicalCoefficient_tangential parameters lower positive row] with radius same contracted
    intro mode
    rw [weightedHilbertTangential_weighted parameters grade _ _ same mode,contracted mode]
    apply PiLp.ext
    intro component
    fin_cases component
    simp [planarComponentMap,smul_smul]
    ring

def SmoothLowPhysicalRow.planar {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (planarCovariantRow lower row) :=
  (curves.bulkUnit (0 : Fin 2) 0).add (curves.bulkUnit (1 : Fin 2) 1)

/-- SAME original S/r has genuine all-grade weighted radial regularity;
the AM12 covariant correction is included before physical reconstruction. -/
def SmoothLowPhysicalRow.originalScalarOverRadius {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {xiOverRadius : DivisionRow 1 lower} {covariant : DivisionRow 3 lower}
    (xi : SmoothLowPhysicalRow parameters lower positive xiOverRadius)
    (curves : SmoothLowPhysicalRow parameters lower positive covariant) :
    SmoothLowPhysicalRow parameters lower positive (originalScalarOverRadiusRow lower positive xiOverRadius covariant) :=
  xi.add curves.planar.tangential.meanFree

end Grad.ActualSmoothPhysicalField
