import AKV20GeneralActualFullSevenCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryLift
open Grad.Constraints.Gauges

/-- The original angular character shift at a fixed Fourier grade. Its
phase is unchanged because the cell frequency is unchanged. -/
def weightedAngularHilbertShift (parameters : PhaseParameters) (dimension grade : ℕ) (shift : ℤ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  coefficientOperator parameters 0 (angularModeTranslation shift)
    (fun mode => annularShiftScalar grade shift mode • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))
    (show 0 ≤ (1+|(shift : ℝ)|)^grade by positivity)
    (fun mode => (ContinuousLinearMap.opNorm_smul_le _ _).trans
      (by
        calc
          _ ≤ ‖annularShiftScalar grade shift mode‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
          _ ≤ _ := by simpa only [mul_one] using annularShiftScalar_norm_le grade shift mode))

theorem weightedAngularHilbertShift_apply (parameters : PhaseParameters) (dimension grade : ℕ) (shift : ℤ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    weightedAngularHilbertShift parameters dimension grade shift field mode =
      annularShiftScalar grade shift mode • field (mode.1-shift, mode.2) := rfl

def planarHilbertComponent (parameters : PhaseParameters) (component : Fin 2) : CellL2 2 →L[ℂ] CellL2 1 :=
  coefficientOperator parameters 0 (Equiv.refl _)
    (fun _ => planarComponentMap component) (norm_nonneg _) (fun _ => le_rfl)

theorem planarHilbertComponent_apply (parameters : PhaseParameters) (component : Fin 2)
    (field : CellL2 2) (mode : ℤ × ℤ) :
    planarHilbertComponent parameters component field mode = planarComponentMap component (field mode) := rfl

def weightedHilbertCosine (parameters : PhaseParameters) (dimension grade : ℕ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  (2 : ℂ)⁻¹ • (weightedAngularHilbertShift parameters dimension grade 1 + weightedAngularHilbertShift parameters dimension grade (-1))

def weightedHilbertSine (parameters : PhaseParameters) (dimension grade : ℕ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  (2*Complex.I : ℂ)⁻¹ • (weightedAngularHilbertShift parameters dimension grade 1 - weightedAngularHilbertShift parameters dimension grade (-1))

def weightedHilbertRadial (parameters : PhaseParameters) (grade : ℕ) : CellL2 2 →L[ℂ] CellL2 1 :=
  (planarHilbertComponent parameters 0).comp (weightedHilbertCosine parameters 2 grade) +
    (planarHilbertComponent parameters 1).comp (weightedHilbertSine parameters 2 grade)

def weightedHilbertTangential (parameters : PhaseParameters) (grade : ℕ) : CellL2 2 →L[ℂ] CellL2 1 :=
  (planarHilbertComponent parameters 1).comp (weightedHilbertCosine parameters 2 grade) -
    (planarHilbertComponent parameters 0).comp (weightedHilbertSine parameters 2 grade)

end Grad.AnnularGeneralSourceRegularity
