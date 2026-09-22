import AJB14GenuineFourierGeneratorExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularOrbitGenerators
open Grad.CartesianState Grad.FourierGrade Grad.AnnularKernelOrbit

variable {H ι : Type*} {V : ι → Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [∀ index, NormedAddCommGroup (V index)] [∀ index, NormedSpace ℂ (V index)]
  [∀ index, NormedSpace ℝ (V index)] [∀ index, IsScalarTower ℝ ℂ (V index)]
  (projection : H →L[ℂ] lp V 2) (orbit : ℝ → H) (smooth : ContDiff ℝ ∞ orbit)
  (frequency : ι → ℤ) (field : lp V 2)
  (character : ∀ time index, projection (orbit time) index = cellExponential (frequency index) time • field index)

include smooth character

/-- Coefficients of the actual generator vector in the complete carrier. -/
theorem smoothLpCharacterOrbit_coordinates (order : ℕ) (index : ι) :
    projection (iteratedDeriv order orbit 0) index =
      (Complex.I * (frequency index : ℂ)) ^ order • field index :=
  smoothCharacterOrbit_generator ((lp.evalCLM ℂ V 2 index).comp projection) orbit smooth
    (frequency index) (field index) (fun time => character time index) order

/-- Genuine Hilbert Fourier-generator domain membership, derived from the
complete norm derivative and bounded coordinate evaluations. -/
theorem smoothLpCharacterOrbit_memℓp (order : ℕ) :
    Memℓp (fun index => (Complex.I * (frequency index : ℂ)) ^ order • field index) 2 := by
  have same : (fun index => (Complex.I * (frequency index : ℂ)) ^ order • field index) =
      fun index => projection (iteratedDeriv order orbit 0) index := by
    funext index
    exact (smoothLpCharacterOrbit_coordinates projection orbit smooth frequency field character order index).symm
  rw [same]
  exact (projection (iteratedDeriv order orbit 0)).property

/-- The generator-domain Hilbert norm is exactly the original coefficient
square sum, with no finite-mode or scalar-coordinate substitute. -/
theorem smoothLpCharacterOrbit_norm_sq (order : ℕ) :
    ‖projection (iteratedDeriv order orbit 0)‖ ^ 2 =
      ∑' index, ‖(Complex.I * (frequency index : ℂ)) ^ order • field index‖ ^ 2 := by
  have squared := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (projection (iteratedDeriv order orbit 0))
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at squared
  rw [squared]
  exact tsum_congr (fun index => congrArg (fun value : V index => ‖value‖ ^ 2)
    (smoothLpCharacterOrbit_coordinates projection orbit smooth frequency field character order index))

end Grad.AnnularOrbitGenerators
