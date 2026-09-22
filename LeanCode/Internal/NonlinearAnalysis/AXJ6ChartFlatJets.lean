import AXJ5SourceFlatJets

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem scalarMean_zero_origin (scalar : ACore parameters 1)
    (mean : angularCore parameters 0 scalar = 0) (cell : ℤ) :
    originValue (scalar.val cell) = 0 := by
  have value := congrArg (fun field : ACore parameters 1 => originValue (field.val cell)) mean
  change originValue (angularClosedJet 0 (scalar.val cell)) = originValue (0 : ClosedJet 1) at value
  rw [angularJet_zero_originValue, originValue_zero] at value
  exact value

theorem scalarGradient_zero_iff (scalar : ACore parameters 1) (cell : ℤ) :
    scalarOriginGradient scalar cell = 0 ↔ ∀ direction, originPartial direction (scalar.val cell) = 0 := by
  constructor
  · intro gradient direction
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    fin_cases direction
    · exact congrArg (fun vector : ComplexEuclidean 2 => vector 0) gradient
    · exact congrArg (fun vector : ComplexEuclidean 2 => vector 1) gradient
  · intro partials
    apply PiLp.ext
    intro direction
    fin_cases direction <;> simp [scalarOriginGradient, planarPair, partials]

theorem rootDerivativeFamily_one_zero (base : TangentCoefficient parameters) :
    rootDerivativeFamily 1 base (fun _ => (0 : TangentCoefficient parameters)) = 0 := by
  have scale := rootDerivativeFamily_one_smul base (0 : TangentCoefficient parameters) (0 : ℂ)
  simpa only [zero_smul] using scale

theorem tameScalarMultiplier_zero_coefficient {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (field : ACore parameters dimension) : tameScalarMultiplier dimension (0 : TameCoefficient parameters) field = 0 := by
  have scale := tameScalarMultiplier_smul dimension (0 : ℂ) (0 : TameCoefficient parameters) field
  simpa only [zero_smul] using scale

theorem tangentComponent_zero (coordinate : Fin 2) :
    tangentComponent (0 : TangentCoefficient parameters) coordinate = 0 := by
  have scale := tangentComponent_smul (0 : ℂ) (0 : TangentCoefficient parameters) coordinate
  simpa only [zero_smul] using scale

theorem chartAffineField_zero_inputs (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (remainder : ACore parameters 3) :
    chartAffineField parameters seed inside 0 0 remainder = remainder := by
  rw [chartAffineField, tangentComponent_zero, tangentComponent_zero,
    tameScalarMultiplier_zero_coefficient, tameScalarMultiplier_zero_coefficient,
    tameScalarMultiplier_zero_coefficient, add_zero, map_zero, zero_add, zero_add]

/-- AL24 on the literal chart derivative, including its original zero-value
conditions, and with the transverse root variation retained until eta=0. -/
theorem chartFlat_iff_jets (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base direction : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (direction.2.1.val cell))
    (mean : angularCore parameters 0 direction.2.2 = 0) :
    (direction.1 = 0 ∧ ∀ cell, scalarOriginGradient direction.2.2 cell = 0) ↔
      ∀ cell, ZeroCartesianFirstJets
          (((chartDerivativeFamily parameters seed inside 1 base (fun _ => direction)).1).val cell) ∧
        ZeroCartesianFirstJets (direction.2.2.val cell) := by
  constructor
  · intro ⟨tangentZero, gradientZero⟩ cell
    constructor
    · rw [chartDerivativeFamily_one_root, tangentZero, rootDerivativeFamily_one_zero,
        chartAffineField_zero_inputs]
      exact zeroJets cell
    · exact zeroFirstJets_of_origin _ (scalarMean_zero_origin direction.2.2 mean cell)
        ((scalarGradient_zero_iff direction.2.2 cell).mp (gradientZero cell))
  · intro jets
    constructor
    · apply Subtype.ext
      funext cell
      have tangent := chartDerivative_one_tangential_gradient seed inside base direction zeroJets cell
      have partialZero (coordinate : Fin 2) : originPartial coordinate
          (((chartDerivativeFamily parameters seed inside 1 base (fun _ => direction)).1).val cell) = 0 :=
        (jets cell).1 1 le_rfl (fun _ => coordinate)
      rw [← tangent]
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;> simp [tangentialOriginGradient, planarPair, partialZero]
    · intro cell
      apply (scalarGradient_zero_iff direction.2.2 cell).mpr
      intro coordinate
      exact (jets cell).2 1 le_rfl (fun _ => coordinate)

end Grad.ChartAxisProjections
