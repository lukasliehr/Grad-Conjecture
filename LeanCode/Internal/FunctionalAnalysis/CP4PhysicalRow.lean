import CP3CircleCharacters

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryTrace Grad.BoundaryLift

/-- The N29 seed-inverted planar field. -/
def rowField (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 2 :=
  (seedInverseCore parameters parameter inside).comp (planarPartCore parameters)

/-- The literal scalar radial boundary contraction of a planar core field. -/
def rowFunction (parameters : PhaseParameters) (field : ACore parameters 2)
    (cell : ℤ) : CellCircle → ℂ :=
  fun angle =>
    ((boundaryCirclePoint angle 0 : ℝ) : ℂ) *
        ((field.1 cell).value (boundaryDiskPoint angle)) 0 +
      ((boundaryCirclePoint angle 1 : ℝ) : ℂ) *
        ((field.1 cell).value (boundaryDiskPoint angle)) 1

theorem rowComponent_continuous (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (index : Fin 2) :
    Continuous (fun angle : CellCircle =>
      ((field.1 cell).value (boundaryDiskPoint angle)) index) :=
  (EuclideanSpace.proj (𝕜 := ℂ) index).continuous.comp
    ((field.1 cell).value.continuous.comp boundaryDiskPoint_continuous)

theorem circleCoordinate_continuous (index : Fin 2) :
    Continuous (fun angle : CellCircle =>
      ((boundaryCirclePoint angle index : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) index).continuous.comp
      boundaryCirclePoint_continuous)

theorem rowFunction_continuous (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    Continuous (rowFunction parameters field cell) :=
  ((circleCoordinate_continuous 0).mul
      (rowComponent_continuous parameters field cell 0)).add
    ((circleCoordinate_continuous 1).mul
      (rowComponent_continuous parameters field cell 1))

/-- The two helicity pieces of the radial contraction. -/
def rowPlusFunction (parameters : PhaseParameters) (field : ACore parameters 2)
    (cell : ℤ) : CellCircle → ℂ :=
  fun angle =>
    ((field.1 cell).value (boundaryDiskPoint angle)) 0 / 2 +
      ((field.1 cell).value (boundaryDiskPoint angle)) 1 / (2 * Complex.I)

def rowMinusFunction (parameters : PhaseParameters) (field : ACore parameters 2)
    (cell : ℤ) : CellCircle → ℂ :=
  fun angle =>
    ((field.1 cell).value (boundaryDiskPoint angle)) 0 / 2 -
      ((field.1 cell).value (boundaryDiskPoint angle)) 1 / (2 * Complex.I)

theorem rowPlusFunction_continuous (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    Continuous (rowPlusFunction parameters field cell) :=
  ((rowComponent_continuous parameters field cell 0).div_const 2).add
    ((rowComponent_continuous parameters field cell 1).div_const (2 * Complex.I))

theorem rowMinusFunction_continuous (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    Continuous (rowMinusFunction parameters field cell) :=
  ((rowComponent_continuous parameters field cell 0).div_const 2).sub
    ((rowComponent_continuous parameters field cell 1).div_const (2 * Complex.I))

/-- The radial contraction against the two first characters. -/
theorem rowFunction_split (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) :
    rowFunction parameters field cell = fun angle =>
      fourier 1 angle * rowPlusFunction parameters field cell angle +
        fourier (-1) angle * rowMinusFunction parameters field cell angle := by
  funext angle
  show ((boundaryCirclePoint angle 0 : ℝ) : ℂ) * _ +
    ((boundaryCirclePoint angle 1 : ℝ) : ℂ) * _ = _
  rw [circle_component_re, circle_component_im]
  show _ = fourier 1 angle *
      (((field.1 cell).value (boundaryDiskPoint angle)) 0 / 2 +
        ((field.1 cell).value (boundaryDiskPoint angle)) 1 / (2 * Complex.I)) +
    fourier (-1) angle *
      (((field.1 cell).value (boundaryDiskPoint angle)) 0 / 2 -
        ((field.1 cell).value (boundaryDiskPoint angle)) 1 / (2 * Complex.I))
  have iNonzero : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

/-- The exact shift decomposition of every radial-contraction coefficient. -/
theorem rowFunction_coefficient (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (m : ℤ) :
    fourierCoeff (rowFunction parameters field cell) m =
      fourierCoeff (rowPlusFunction parameters field cell) (m - 1) +
        fourierCoeff (rowMinusFunction parameters field cell) (m + 1) := by
  rw [rowFunction_split]
  rw [fourierCoeff_add_continuous
    (fun angle => fourier 1 angle * rowPlusFunction parameters field cell angle)
    (fun angle => fourier (-1) angle * rowMinusFunction parameters field cell angle)
    m
    ((fourier 1).continuous.mul (rowPlusFunction_continuous parameters field cell))
    ((fourier (-1)).continuous.mul (rowMinusFunction_continuous parameters field cell))]
  rw [fourierCoeff_character_shift 1 m (rowPlusFunction parameters field cell),
    fourierCoeff_character_shift (-1) m (rowMinusFunction parameters field cell),
    show m - -1 = m + 1 by ring]

/-- The plus piece against the accepted boundary coefficients. -/
theorem rowPlusFunction_coefficient (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (k : ℤ) :
    fourierCoeff (rowPlusFunction parameters field cell) k =
      originalBoundaryCoefficient parameters field (k, cell) 0 / 2 +
        originalBoundaryCoefficient parameters field (k, cell) 1 / (2 * Complex.I) := by
  have expand : rowPlusFunction parameters field cell = fun angle =>
      (1 / 2 : ℂ) * ((field.1 cell).value (boundaryDiskPoint angle)) 0 +
        (1 / (2 * Complex.I)) * ((field.1 cell).value (boundaryDiskPoint angle)) 1 := by
    funext angle
    show _ / 2 + _ / (2 * Complex.I) = _
    ring
  rw [expand]
  rw [fourierCoeff_add_continuous
    (fun angle => (1 / 2 : ℂ) * ((field.1 cell).value (boundaryDiskPoint angle)) 0)
    (fun angle => (1 / (2 * Complex.I)) *
      ((field.1 cell).value (boundaryDiskPoint angle)) 1)
    k
    (continuous_const.mul (rowComponent_continuous parameters field cell 0))
    (continuous_const.mul (rowComponent_continuous parameters field cell 1))]
  rw [fourierCoeff_const_mul, fourierCoeff_const_mul,
    fourierCoeff_component parameters field cell k 0,
    fourierCoeff_component parameters field cell k 1]
  ring

/-- The minus piece against the accepted boundary coefficients. -/
theorem rowMinusFunction_coefficient (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (k : ℤ) :
    fourierCoeff (rowMinusFunction parameters field cell) k =
      originalBoundaryCoefficient parameters field (k, cell) 0 / 2 -
        originalBoundaryCoefficient parameters field (k, cell) 1 / (2 * Complex.I) := by
  have expand : rowMinusFunction parameters field cell = fun angle =>
      (1 / 2 : ℂ) * ((field.1 cell).value (boundaryDiskPoint angle)) 0 +
        (-(1 / (2 * Complex.I))) * ((field.1 cell).value (boundaryDiskPoint angle)) 1 := by
    funext angle
    show _ / 2 - _ / (2 * Complex.I) = _
    ring
  rw [expand]
  rw [fourierCoeff_add_continuous
    (fun angle => (1 / 2 : ℂ) * ((field.1 cell).value (boundaryDiskPoint angle)) 0)
    (fun angle => (-(1 / (2 * Complex.I))) *
      ((field.1 cell).value (boundaryDiskPoint angle)) 1)
    k
    (continuous_const.mul (rowComponent_continuous parameters field cell 0))
    (continuous_const.mul (rowComponent_continuous parameters field cell 1))]
  rw [fourierCoeff_const_mul, fourierCoeff_const_mul,
    fourierCoeff_component parameters field cell k 0,
    fourierCoeff_component parameters field cell k 1]
  ring

end Grad.Cor18
