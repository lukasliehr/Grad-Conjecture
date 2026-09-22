import AHQ6FixedRadialKernelRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives

variable {X : Type*} [TopologicalSpace X]

theorem rowMultiplicationEntry_continuous (dimension : ℕ)
    (coefficients : X → Fin dimension → ℤ × ℤ → ℂ)
    (continuousCoefficients : ∀ component shift, Continuous (fun x => coefficients x component shift))
    (shift input : ℤ × ℤ) : Continuous (fun x => rowMultiplicationEntry dimension (coefficients x) shift input) := by
  unfold rowMultiplicationEntry
  apply continuous_finsetSum
  intro component _
  exact (continuousCoefficients component shift).smul continuous_const

theorem matrixMultiplicationEntry_continuous (src tgt : ℕ)
    (coefficients : X → Fin tgt → Fin src → ℤ × ℤ → ℂ)
    (continuousCoefficients : ∀ row column shift, Continuous (fun x => coefficients x row column shift))
    (shift input : ℤ × ℤ) : Continuous (fun x => matrixMultiplicationEntry src tgt (coefficients x) shift input) := by
  unfold matrixMultiplicationEntry
  apply continuous_finsetSum
  intro row _
  apply continuous_finsetSum
  intro column _
  exact (continuousCoefficients row column shift).smul continuous_const

section Actual
variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)

theorem radialGaugeCoefficients_continuous (kind : Fin 2) (component : Fin 3)
    (radial : ℕ) (shift : ℤ × ℤ) :
    Continuous (fun r : RadialPoint => radialGaugeCoefficients parameters L compact state r kind component radial shift) := by
  have all : Continuous (fun radius => gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low kind component radial radius shift) :=
    continuous_iff_continuousAt.mpr (fun radius =>
      (gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low kind component radial radius shift).continuousAt)
  exact all.comp continuous_subtype_val

theorem radialSigmaCoefficients_continuous (component : Fin 3) (radial : ℕ) (shift : ℤ × ℤ) :
    Continuous (fun r : RadialPoint => radialSigmaCoefficients parameters L compact state r component radial shift) := by
  have all : Continuous (fun radius => sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low component radial radius shift) :=
    continuous_iff_continuousAt.mpr (fun radius =>
      (sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon state.data.field state.low component radial radius shift).continuousAt)
  exact all.comp continuous_subtype_val

theorem radialForceKernel_regular (kind : Fin 2) (radial : ℕ) :
    RegularKernelFamily (fun r : RadialPoint => radialForceKernel parameters L compact state r kind radial) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => radialForceKernel_moment_le parameters L compact state r kind radial moment)
  intro shift input
  refine rowMultiplicationEntry_continuous (X := RadialPoint) 3
    (fun r component mode => forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component radial r.val mode) ?_ shift input
  intro component mode
  exact (forceScalar_continuous parameters L state.data.rho state.data.epsilon state.data.field kind state.low component radial mode).comp continuous_subtype_val

theorem radialGaugeRowsKernel_regular (radial : ℕ) :
    RegularKernelFamily (fun r : RadialPoint => radialGaugeRowsKernel parameters L compact state r radial) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => radialGaugeRowsKernel_moment_le parameters L compact state r radial moment)
  intro shift input
  exact matrixMultiplicationEntry_continuous 3 2
    (fun r kind component mode => radialGaugeCoefficients parameters L compact state r kind component radial mode)
    (radialGaugeCoefficients_continuous parameters L compact state · · radial ·) shift input

theorem radialSigmaKernel_regular (radial : ℕ) :
    RegularKernelFamily (fun r : RadialPoint => radialSigmaKernel parameters L compact state r radial) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => radialSigmaKernel_moment_le parameters L compact state r radial moment)
  intro shift input
  exact rowMultiplicationEntry_continuous 3
    (fun r component mode => radialSigmaCoefficients parameters L compact state r component radial mode)
    (radialSigmaCoefficients_continuous parameters L compact state · radial ·) shift input

end Actual
end Grad.AnnularKernelContinuity
