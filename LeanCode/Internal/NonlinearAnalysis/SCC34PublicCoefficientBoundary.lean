import SCC33ActualCoefficientRecovery

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation

theorem kappaScalar_hasDerivAt (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (mode : ℤ × ℤ) (radial : ℕ) (radius : ℝ) :
    HasDerivAt (fun radius => kappaScalar parameters L rho epsilon field low component radial radius mode)
      (kappaScalar parameters L rho epsilon field low component (radial + 1) radius mode) radius :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (kappaFourier_hasDerivAt parameters L rho epsilon field low component mode radial radius)

/-- The full radial derivative tower is genuine ordinary differentiation of
the smooth coefficient extension, whose values on the original closed disk
are the physical double Fourier integrals by actualKappa_doubleCoefficient. -/
theorem kappaScalar_iteratedDeriv (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (mode : ℤ × ℤ) (radial : ℕ) :
    iteratedDeriv radial (fun radius => kappaScalar parameters L rho epsilon field low component 0 radius mode) =
      fun radius => kappaScalar parameters L rho epsilon field low component radial radius mode := by
  induction radial with
  | zero => exact iteratedDeriv_zero
  | succ radial previous =>
    rw [iteratedDeriv_succ, previous]
    funext radius
    exact (kappaScalar_hasDerivAt parameters L rho epsilon field low component mode radial radius).deriv

/-- BS40 at the exact t+k+5 budget. The single positive B6 neighborhood is
fixed before both derivative grades and before the physical state. -/
theorem actualBS40CoefficientBound (parameters : PhaseParameters) (L : ℝ) :
    0 < originalCoefficientLowRadius parameters L ∧
    ∀ tangential radial : ℕ, ∃ bound : ℝ, 0 < bound ∧
      ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
        (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
        (component : Fin 3) (radius : ℝ), 0 < radius → radius ≤ 1 →
        Summable (productMoment parameters tangential radius
          (fun mode => iteratedDeriv radial (fun r => kappaScalar parameters L rho epsilon field low component 0 r mode) radius)) ∧
        (∑' mode, productMoment parameters tangential radius
          (fun mode => iteratedDeriv radial (fun r => kappaScalar parameters L rho epsilon field low component 0 r mode) radius) mode) ≤
          bound * physicalBudget parameters field rho epsilon (tangential + radial + 5) := by
  refine ⟨originalCoefficientLowRadius_positive parameters L, ?_⟩
  intro tangential radial
  refine ⟨kappaFourierConstant parameters L tangential radial, kappaFourierConstant_pos _ _ _ _, ?_⟩
  intro rho epsilon field low component radius positive bounded
  simp_rw [kappaScalar_iteratedDeriv]
  exact ⟨kappaScalarMoment_summable parameters L rho epsilon field low component tangential radial radius positive.le bounded,
    kappaScalarMoment_bound parameters L rho epsilon field low component tangential radial radius positive.le bounded⟩

end Grad.SourceCollarCoefficients
