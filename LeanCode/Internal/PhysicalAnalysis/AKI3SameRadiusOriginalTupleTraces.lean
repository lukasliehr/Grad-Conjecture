import AKI2LiteralFourFieldSmoothCarrier
import AJG2SameBulkNegativeKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularVariational
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularPhysicalReconstruction

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)

def tupleWeightedCurve (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4) :
    ℕ → ℝ → CellL2 1 := Classical.choose (tuple.property.1 slot).2

theorem tupleWeightedCurve_smooth (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (grade : ℕ) : ContDiffOn ℝ ∞ (tupleWeightedCurve parameters lower tuple slot grade) (Icc lower 1) :=
  (Classical.choose_spec (tuple.property.1 slot).2).1 grade

theorem tupleWeightedCurve_coefficient (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleWeightedCurve parameters lower tuple slot grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          originalPhysicalCoefficient (tuple.val slot) radius mode) :=
  (Classical.choose_spec (tuple.property.1 slot).2).2 grade radius inside mode

def tupleRadius (radius : Icc lower (1 : ℝ)) : RadialPoint :=
  ⟨radius.val, positive.le.trans radius.property.1, radius.property.2⟩

def tupleNegativeTrace (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (radius : Icc lower (1 : ℝ)) : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 1 :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) 1
    (tupleWeightedCurve parameters lower tuple slot 0 radius.val)

theorem tupleNegativeTrace_coefficient (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleNegativeTrace parameters lower positive tuple slot radius) mode =
        originalPhysicalCoefficient (tuple.val slot) radius.val mode := by
  rw [tupleNegativeTrace, bulkNegativeLift_coefficient,
    tupleWeightedCurve_coefficient parameters lower tuple slot 0 radius.val radius.property]
  simp only [pow_zero, Complex.ofReal_one, one_smul]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _

def tupleDifferentiatedTrace (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (axis : Bool) (radius : Icc lower (1 : ℝ)) :
    NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 1 :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) 1
    (hilbertFrequencyOperator parameters 1 (some axis)
      (tupleWeightedCurve parameters lower tuple slot 1 radius.val))

theorem tupleDifferentiatedTrace_coefficient (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (axis : Bool) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleDifferentiatedTrace parameters lower positive tuple slot axis radius) mode =
        frequencyNumerator (some axis) mode • originalPhysicalCoefficient (tuple.val slot) radius.val mode := by
  rw [tupleDifferentiatedTrace, bulkNegativeLift_coefficient, hilbertFrequencyOperator_apply,
    tupleWeightedCurve_coefficient parameters lower tuple slot 1 radius.val radius.property]
  have frequency : ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 1 : ℝ) : ℂ) =
      ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ (0 + 1) : ℝ) : ℂ) := rfl
  rw [frequency, frequencyRatio_weighted]
  simp only [pow_zero, Complex.ofReal_one, one_smul]
  rw [smul_comm (frequencyNumerator (some axis) mode)]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _

/-- The original seven slots are Rp, Rxi, ∂ζxi, xi, F0, RF0, F2.
Only the accepted normalization later divides the two xi slots by radius. -/
def tupleSevenInput (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ)) :
    SevenSlotTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 :=
  WithLp.toLp 2 ![tupleDifferentiatedTrace parameters lower positive tuple 0 false radius,
    tupleDifferentiatedTrace parameters lower positive tuple 1 false radius,
    tupleDifferentiatedTrace parameters lower positive tuple 1 true radius,
    tupleNegativeTrace parameters lower positive tuple 1 radius,
    tupleNegativeTrace parameters lower positive tuple 2 radius,
    tupleDifferentiatedTrace parameters lower positive tuple 2 false radius,
    tupleNegativeTrace parameters lower positive tuple 3 radius]

theorem tupleSevenInput_supported (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ)) :
    IsAngularMeanFree (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleSevenInput parameters lower positive tuple radius 0) := by
  intro cell
  change negativeTraceCoefficient _ 0 0 (tupleDifferentiatedTrace parameters lower positive tuple 0 false radius) (0, cell) = 0
  rw [tupleDifferentiatedTrace_coefficient]
  simp [frequencyNumerator]

theorem tupleSevenInput_scalarDerivative (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ)) :
    IsAngularDerivative (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleSevenInput parameters lower positive tuple radius 3)
      (tupleSevenInput parameters lower positive tuple radius 1) := by
  intro mode
  change negativeTraceCoefficient _ 0 0 (tupleDifferentiatedTrace parameters lower positive tuple 1 false radius) mode = _
  rw [tupleDifferentiatedTrace_coefficient]
  change frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 1) radius.val mode =
    (Complex.I * (mode.1 : ℂ)) • negativeTraceCoefficient _ 0 0 (tupleNegativeTrace parameters lower positive tuple 1 radius) mode
  rw [tupleNegativeTrace_coefficient]
  rfl

end Grad.AnnularOriginalSmoothCore
