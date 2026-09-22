import AKBB4SameCorrectedPRadialCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.ActualPolarFlux
open Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.SourceCollarCoefficients

/-- Literal determinant symbol after the true angular primitive. -/
def primitiveDeterminantModeRHS (length radius : ℝ) (mode : ℤ × ℤ)
    (values : Fin 4 → ComplexEuclidean 1) : ComplexEuclidean 1 :=
  (if mode.1 = 0 then (0 : ℂ) else 1) •
    ((-((radius : ℂ)⁻¹)) • values 0 -
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • values 1) -
      (radius : ℂ)⁻¹ • values 2 + values 3)

private theorem primitiveSymbolAlgebra (inverse angular axial radial length : ℂ)
    (one : inverse * angular = 1) (x b v g : ComplexEuclidean 1) :
    inverse • ((-radial) • x - length • (axial • (angular • b)) -
      radial • (angular • v) + angular • g) =
      (-radial) • (inverse • x) - length • (axial • b) - radial • v + g := by
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.smul_apply,PiLp.sub_apply,PiLp.add_apply,smul_eq_mul]
  linear_combination (-length * axial * b coordinate - radial * v coordinate + g coordinate) * one

/-- The zero angular mode remains projected away, and c=Rb3 gives exactly
the original mean-free p equation without any angular integration constant. -/
theorem primitiveDeterminantModeRHS_eq (length radius : ℝ) (mode : ℤ × ℤ)
    (original primitive : Fin 4 → ComplexEuclidean 1)
    (p : primitive 0 = angularInverseMultiplier mode • original 0)
    (c : original 1 = (Complex.I * (mode.1 : ℂ)) • primitive 1)
    (v : original 2 = primitive 2) (g : original 3 = primitive 3) :
    angularInverseMultiplier mode • determinantModeRHS length radius mode original =
      primitiveDeterminantModeRHS length radius mode primitive := by
  by_cases zero : mode.1=0
  · simp [determinantModeRHS,primitiveDeterminantModeRHS,zero]
  · simp only [determinantModeRHS,primitiveDeterminantModeRHS,if_neg zero,one_smul,
      frequencyNumerator,p,c,v,g]
    apply primitiveSymbolAlgebra
    simp only [angularInverseMultiplier,if_neg zero]
    exact inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero))

end Grad.ActualPolarFlux
