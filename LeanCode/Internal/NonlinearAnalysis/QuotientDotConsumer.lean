import QuotientBilinearBound

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial

/-- The complex-bilinear physical dot product, placed in the one-dimensional
complex Euclidean coefficient space. No conjugation is inserted. -/
def physicalDotProduct : ContinuousMultilinearMap ℂ
    (fun _ : Fin 2 => ComplexEuclidean 3) (ComplexEuclidean 1) :=
  ∑ coordinate : Fin 3,
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ 2 ℂ).compContinuousLinearMap
      (fun _ => PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) coordinate)).smulRight
        (EuclideanSpace.single 0 1)

theorem physicalDotProduct_value (first second : ComplexEuclidean 3) :
    physicalDotProduct ![first, second] 0 = Grad.NonlinearQuotient.complexDot first second := by
  simp [physicalDotProduct, Grad.NonlinearQuotient.complexDot,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

def nonlinearRadialCore (parameters : PhaseParameters)
    (first second : ACore parameters 3) : ACore parameters 1 :=
  bilinearRadialCore parameters physicalDotProduct first second

def nonlinearRadialConstant (grade : ℕ) : ℝ := radialQuotientConstant grade * ‖physicalDotProduct‖

theorem nonlinearRadialConstant_nonnegative (grade : ℕ) : 0 ≤ nonlinearRadialConstant grade :=
  mul_nonneg (radialQuotientConstant_nonnegative _) (norm_nonneg _)

/-- Q3 for the actual I Δ Π(Dv₁ · Rv₂) core, with the literal complex-bilinear
dot product and exactly high q+6 / low4. -/
theorem nonlinearRadialCore_bound (parameters : PhaseParameters)
    (first second : ACore parameters 3) (grade : ℕ) :
    originalGradeNorm grade (nonlinearRadialCore parameters first second) ≤
      nonlinearRadialConstant grade *
        (originalGradeNorm (grade + 6) first * originalGradeNorm 4 second +
          originalGradeNorm 4 first * originalGradeNorm (grade + 6) second) :=
  bilinearRadialCore_bound parameters physicalDotProduct first second grade

/-- Immediate literal convolution consumer: each physical product summand
is Dv₁·Rv₂, with the original Fourier cell sum and no inserted conjugates. -/
theorem physicalEulerRotationProduct_coefficient (parameters : PhaseParameters)
    (first second : ACore parameters 3) (cell : ℤ) (point : ClosedDisk) :
    ((actualMultilinearProduct parameters physicalDotProduct
      ![eulerCore parameters first, rotationCore parameters second]).val cell).value point =
      productCoefficientValue physicalDotProduct
        ![eulerCore parameters first, rotationCore parameters second] cell point :=
  actualMultilinearProduct_isActual parameters physicalDotProduct
    ![eulerCore parameters first, rotationCore parameters second] cell point

end Grad.NonlinearQuotientBounds
