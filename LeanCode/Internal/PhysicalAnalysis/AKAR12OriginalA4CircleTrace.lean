import AKAR11OriginalCircleBessel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients
open Grad.OriginalFlatAxisDecay

variable {dimension : ℕ}

def originalFlatCircleCell (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (cell : ℤ) (angle : ℝ) :
    ComplexEuclidean dimension :=
  let point := polarClosedPoint radius.val angle radius.property.1 radius.property.2
  if rotated then originalFlatRotationVector parameters field flat point cell
  else originalFlatValueVector parameters field flat point cell

theorem originalFlatCircleCell_continuous (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (cell : ℤ) :
    Continuous (originalFlatCircleCell parameters field flat radius rotated cell) := by
  have point : Continuous (fun angle => polarClosedPoint radius.val angle radius.property.1 radius.property.2) :=
    (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  cases rotated
  · change Continuous (fun angle => (cellFrequency cell : ℂ) • completedWeightedCell parameters (by omega) cell field
      (polarClosedPoint radius.val angle radius.property.1 radius.property.2))
    exact ((completedWeightedCell parameters (by omega) cell field).continuous.comp point).const_smul (cellFrequency cell : ℂ)
  · have derivative (direction : Fin 2) :=
      (completedCellDerivative parameters 1 (fun _ => direction) cell field).continuous.comp point
    have weight := (originalWeightContinuous parameters cell).continuous.comp point
    have coordinate (direction : Fin 2) : Continuous (fun angle =>
        ((polarClosedPoint radius.val angle radius.property.1 radius.property.2).val direction : ℂ)) := by
      exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) direction).comp
        (continuous_subtype_val.comp point))
    change Continuous (fun angle => (cellFrequency cell : ℂ) •
      ((cartesianWeight parameters cell (polarClosedPoint radius.val angle radius.property.1 radius.property.2).val : ℂ) •
        (((polarClosedPoint radius.val angle radius.property.1 radius.property.2).val 0 : ℂ) •
          completedCellDerivative parameters 1 (fun _ => 1) cell field (polarClosedPoint radius.val angle radius.property.1 radius.property.2) -
        ((polarClosedPoint radius.val angle radius.property.1 radius.property.2).val 1 : ℂ) •
          completedCellDerivative parameters 1 (fun _ => 0) cell field (polarClosedPoint radius.val angle radius.property.1 radius.property.2))))
    have result := (weight.smul (((coordinate 0).smul (derivative 1)).sub ((coordinate 1).smul (derivative 0)))).const_smul (cellFrequency cell : ℂ)
    exact result

def originalFlatCircleConstant (parameters : PhaseParameters) (field : AGrade parameters dimension 4) (radius : RadialPoint) : ℝ :=
  flatDecayConstant * radius.val^(3/2:ℝ) * ‖field‖

theorem originalFlatCircleConstant_nonnegative (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (radius : RadialPoint) : 0 ≤ originalFlatCircleConstant parameters field radius :=
  mul_nonneg (mul_nonneg flatDecayConstant_nonnegative (Real.rpow_nonneg radius.property.1 _)) (norm_nonneg _)

theorem originalFlatCircleCell_energy (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (cells : Finset ℤ) (angle : ℝ) :
    ∑ cell ∈ cells, ‖originalFlatCircleCell parameters field flat radius rotated cell angle‖^2 ≤
      (originalFlatCircleConstant parameters field radius)^2 := by
  let point := polarClosedPoint radius.val angle radius.property.1 radius.property.2
  have pointNorm : ‖point.val‖ = radius.val := (polarPlane_norm radius.val angle).trans (abs_of_nonneg radius.property.1)
  have flatBound := originalA4_flat_decay parameters field flat point
  rw [pointNorm] at flatBound
  have finiteBound (vector : lp (fun _ : ℤ => ComplexEuclidean dimension) 2)
      (bound : ‖vector‖ ≤ originalFlatCircleConstant parameters field radius) :
      ∑ cell ∈ cells, ‖vector cell‖^2 ≤ (originalFlatCircleConstant parameters field radius)^2 := by
    have sum : HasSum (fun cell : ℤ => ‖vector cell‖^2) (‖vector‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) vector
    exact ((sum.summable.sum_le_tsum cells (fun _ _ => sq_nonneg _)).trans_eq sum.tsum_eq).trans
      (pow_le_pow_left₀ (norm_nonneg _) bound 2)
  cases rotated
  · exact finiteBound (originalFlatValueVector parameters field flat point) (by
      change _ ≤ flatDecayConstant * radius.val^(3/2:ℝ)*‖field‖
      linarith [norm_nonneg (originalFlatRotationVector parameters field flat point)])
  · exact finiteBound (originalFlatRotationVector parameters field flat point) (by
      change _ ≤ flatDecayConstant * radius.val^(3/2:ℝ)*‖field‖
      linarith [norm_nonneg (originalFlatValueVector parameters field flat point)])

/-- Original A4 circle membership is proved from the actual finite-cell Bessel
estimate. No completed annular graph or width-shrunk trace is postulated. -/
def originalA4CircleTrace (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) : CellL2 dimension :=
  originalCircleFamilyVector (originalFlatCircleCell parameters field flat radius rotated)
    (originalFlatCircleCell_continuous parameters field flat radius rotated)
    (originalFlatCircleConstant parameters field radius)
    (originalFlatCircleCell_energy parameters field flat radius rotated)

theorem originalA4CircleTrace_bound (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) :
    ‖originalA4CircleTrace parameters field flat radius rotated‖ ≤
      flatDecayConstant * radius.val^(3/2:ℝ) * ‖field‖ :=
  originalCircleFamilyVector_bound _ _ _ (originalFlatCircleConstant_nonnegative parameters field radius) _

theorem originalA4CircleTrace_coefficient (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (mode : ℤ × ℤ) :
    originalA4CircleTrace parameters field flat radius rotated mode =
      angularCoefficient (originalFlatCircleCell parameters field flat radius rotated mode.2) mode.1 := rfl

end Grad.OriginalKernelRetainedDecay
