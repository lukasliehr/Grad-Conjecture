import AXL17RootReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ComplexConjugate

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates Grad.ChartAxisSplit
open Grad.CompletedReality Grad.Q24Realization Grad.RealFixedRanges Grad.Cor18

variable {parameters : PhaseParameters}

theorem core_real_of_real_factor {dimension : ℕ} (first second : ACore parameters dimension)
    (factor : ClosedDisk → ℝ)
    (law : ∀ cell point, (first.val cell).value point = (factor point : ℂ) • (second.val cell).value point)
    (real : cartesianCoreConjugation parameters second = second) :
    cartesianCoreConjugation parameters first = first := by
  apply acore_ext
  intro cell point
  have secondReal := congrArg (fun field : ACore parameters dimension => (field.val cell).value point) real
  change cartesianPhysicalConjugation dimension ((second.val (-cell)).value point) =
    (second.val cell).value point at secondReal
  change cartesianPhysicalConjugation dimension ((first.val (-cell)).value point) =
    (first.val cell).value point
  rw [law, law, Complex.coe_smul, Complex.coe_smul, map_smul, secondReal]

theorem capScalarCoordinate_real (radius : ℝ) (positive : 0 < radius) (coordinate : Fin 2) :
    cartesianCoreConjugation parameters (capScalarCoordinate parameters radius positive coordinate) =
      capScalarCoordinate parameters radius positive coordinate :=
  core_real_of_real_factor _ (tameCoordinateScalarField parameters coordinate)
    (fun point => radialCap radius positive point.val)
    (fun cell point => capCoordinateCore_value_factor parameters radius positive coordinate _ cell point)
    (tameCoordinateScalarField_real coordinate)

theorem capScalarAffine_real (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) (real : RealTangent sigma) :
    cartesianCoreConjugation parameters (capScalarAffine parameters radius positive sigma) =
      capScalarAffine parameters radius positive sigma := by
  rw [capScalarAffine, map_add, tameScalarMultiplier_conjugate _ (fun cell => real cell 0),
    tameScalarMultiplier_conjugate _ (fun cell => real cell 1), capScalarCoordinate_real, capScalarCoordinate_real]

theorem chartAffineField_real (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (realC : ∀ cell, coefficient.val (-cell) = conj (coefficient.val cell))
    (tangent : TangentCoefficient parameters) (realT : RealTangent tangent) :
    cartesianCoreConjugation parameters (chartAffineField parameters seed inside coefficient tangent 0) =
      chartAffineField parameters seed inside coefficient tangent 0 := by
  rw [chartAffineField, add_zero, map_add, tameScalarMultiplier_conjugate _ realC, tameSeedField_real,
    valueMapCore_conjugate tameTangentInclusion tameTangentInclusion_real,
    map_add, tameScalarMultiplier_conjugate _ (fun cell => realT cell 0),
    tameScalarMultiplier_conjugate _ (fun cell => realT cell 1),
    tameCoordinateScalarField_real, tameCoordinateScalarField_real]

theorem capAffineField_real (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (realC : ∀ cell, coefficient.val (-cell) = conj (coefficient.val cell))
    (tangent : TangentCoefficient parameters) (realT : RealTangent tangent) :
    cartesianCoreConjugation parameters (capAffineField parameters radius positive seed inside coefficient tangent) =
      capAffineField parameters radius positive seed inside coefficient tangent :=
  core_real_of_real_factor _ (chartAffineField parameters seed inside coefficient tangent 0)
    (fun point => radialCap radius positive point.val)
    (capAffineField_value_factor radius positive seed inside coefficient tangent)
    (chartAffineField_real seed inside coefficient realC tangent realT)

theorem storedCapChartRemainder_real (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (realC : ∀ cell, coefficient.val (-cell) = conj (coefficient.val cell))
    (tangent : TangentCoefficient parameters) (realT : RealTangent tangent) :
    cartesianCoreConjugation parameters
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) =
      storedCapChartRemainder parameters radius positive seed inside coefficient tangent := by
  rw [storedCapChartRemainder, toPhysicalCore_conjugate, capChartRemainder, map_sub,
    capAffineField_real radius positive seed inside coefficient realC tangent realT,
    chartAffineField_real seed inside coefficient realC tangent realT]

/-- Identity on the literal axis coefficients, into the existing state carrier. -/
def tangentToStateAxis (parameters : PhaseParameters) :
    TangentCoefficient parameters →ₗ[ℂ] Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) where
  toFun family := ⟨family.val, fun grade => by
    apply (memlp_iff_summable_sq _).2
    apply (family.property grade).congr
    intro cell
    rw [tangentTerm_eq_axis]
    change _ = ‖(Grad.AxisCore.axisWeight parameters grade cell : ℂ) • family.val cell‖ ^ 2
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Grad.AxisCore.axisWeight_pos parameters grade cell), mul_pow]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothingToTangent_stateAxis (family : TangentCoefficient parameters) :
    smoothingToTangent parameters (tangentToStateAxis parameters family) = family := rfl

def capLiftState (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (sigma tangent : TangentCoefficient parameters) :
    Grad.SmoothingFamily.StateCore parameters :=
  (tangentToStateAxis parameters tangent,
    storedCapChartRemainder parameters radius positive seed inside coefficient tangent,
    capScalarAffine parameters radius positive sigma)

theorem capLiftState_mem (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (realC : ∀ cell, coefficient.val (-cell) = conj (coefficient.val cell))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    capLiftState parameters radius positive seed inside coefficient sigma tangent ∈ stateSmoothRange parameters seed inside := by
  apply (mem_stateSmoothRange parameters seed inside _).2
  constructor
  · apply fullProjection_fixes
    exact ⟨storedCapChartRemainder_vectorConstraints radius positive bounded seed inside coefficient tangent,
      capScalarAffine_mean_zero parameters radius positive sigma⟩
  · apply Prod.ext
    · apply Subtype.ext
      funext cell
      apply PiLp.ext
      intro index
      change conj (tangent.val (-cell) index) = tangent.val cell index
      rw [realT, Complex.conj_conj]
    · exact Prod.ext (storedCapChartRemainder_real radius positive seed inside coefficient realC tangent realT)
        (capScalarAffine_real radius positive sigma realS)

end Grad.ChartAxisLift
