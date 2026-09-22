import AHS14SameSevenSlotForceData

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

private abbrev rp (parameters : PhaseParameters) (r : RadialPoint) := radialKernelParameters parameters r

theorem radialSevenFreeChartRotation_tail (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    forceCoordinateTrace (rp parameters r) angular cell 1
      (radialSevenFreeChartRotation parameters r angular cell mass input) = input 1 ∧
    forceCoordinateTrace (rp parameters r) angular cell 2
      (radialSevenFreeChartRotation parameters r angular cell mass input) = 0 := by
  constructor
  all_goals
    apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
    intro mode
    apply PiLp.ext
    intro component
    have unique := Fin.eq_zero component
    subst component
    simp only [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient,
      radialSevenFreeChartRotation, negativeTraceCoefficient_add, PiLp.add_apply,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, coordinateInjectionKernel_action_coefficient]
    simp [Fin.ext_iff, negativeTraceCoefficient]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialSevenEncodedTrace_force (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell (input 2))
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell (input 6)) :
    let encoded := radialSevenEncodedTrace parameters L compact state r small angular cell mass input
    let known := radialSevenFreeChart parameters r angular cell mass input
    let gaugeSmall := small.trans (min_le_left _ _)
    EncodedSupport (rp parameters r) angular cell encoded ∧
      radialFirstForceTrace parameters L compact state r gaugeSmall angular cell encoded known = input 4 ∧
      radialThirdForceTrace parameters L compact state r gaugeSmall angular cell encoded known (input 2) = input 6 := by
  have forces := radialEncodedFirstInverse_solves_force parameters L compact state r small angular cell
    (radialSevenFreeChart parameters r angular cell mass input)
    (radialSevenFreeChartRotation parameters r angular cell mass input)
    (input 2) (input 4) (input 5) (input 6)
    (radialSevenFreeChart_first_meanFree parameters r angular cell mass input)
    (radialSevenFreeChart_derivative parameters r angular cell mass input massMean scalarLaw)
    sourceLaw xiZetaMean sourceTwoMean
  dsimp only at forces ⊢
  rw [← radialSevenEncodedTrace_eq_inverse parameters L compact state r small angular cell mass input massMean] at forces
  exact forces

/-- Literal full normalized physical first/third rows of the same stored
covariant and genuine rotation, retaining -2a1, +Rxi/r and -L^-1 xi_zeta. -/
theorem radialSevenCovariant_force_rows (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell (input 2))
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell (input 6)) :
    let covariant := fullNegativeKernelAction (rp parameters r) angular cell
      (radialUnknownUKernel parameters L compact state r small) mass +
      fullNegativeKernelAction (rp parameters r) angular cell (radialKnownAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)
    let rotated := fullNegativeKernelAction (rp parameters r) angular cell
      (radialUnknownVKernel parameters L compact state r small) mass +
      fullNegativeKernelAction (rp parameters r) angular cell (radialKnownRAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)
    (-forceCoordinateTrace (rp parameters r) angular cell 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 covariant +
      fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) covariant +
      input 1 = input 4) ∧
    (forceCoordinateTrace (rp parameters r) angular cell 2 rotated +
      forceMeanFreeTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0) covariant) -
      (L : ℂ)⁻¹ • input 2 = input 6) := by
  have forces := radialSevenEncodedTrace_force parameters L compact state r small angular cell mass input
    massMean scalarLaw sourceLaw xiZetaMean sourceTwoMean
  dsimp only at forces ⊢
  rw [← radialSevenEncodedTrace_same_covariant parameters L compact state r small angular cell mass input,
    ← radialSevenEncodedTrace_same_rotation parameters L compact state r small angular cell mass input]
  constructor
  · calc
      _ = radialFirstForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell
          (radialSevenEncodedTrace parameters L compact state r small angular cell mass input)
          (radialSevenFreeChart parameters r angular cell mass input) := by
        unfold radialFirstForceTrace radialForceChartRotation
        rw [map_add, (radialSevenFreeChartRotation_tail parameters r angular cell mass input).1]
        abel
      _ = input 4 := forces.2.1
  · calc
      _ = radialThirdForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell
          (radialSevenEncodedTrace parameters L compact state r small angular cell mass input)
          (radialSevenFreeChart parameters r angular cell mass input) (input 2) := by
        unfold radialThirdForceTrace radialForceChartRotation
        rw [map_add, (radialSevenFreeChartRotation_tail parameters r angular cell mass input).2, add_zero,
          encodedRotation_third, angularMeanFreeKernel_action_eq _ _ _ _
            (forceCoordinate_meanFree (rp parameters r) angular cell _ 2 forces.1.2.2)]
      _ = input 6 := forces.2.2

end Grad.AnnularReconstruction
