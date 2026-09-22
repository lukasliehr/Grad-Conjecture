import AKAO17OriginalCofactorJetSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row component : Fin 3)
    (radial : Fin 2) (r : RadialPoint)

theorem originalCofactorTerm_angular (mode : ℤ × ℤ) (polar axial : ℝ) :
    HasDerivAt (fun angle => cellExponential mode.2 axial *
      (cellExponential mode.1 angle * radialCofactorJetScalar parameters length compact state row component radial 0 r mode))
      (cellExponential mode.2 axial * (cellExponential mode.1 polar *
        radialCofactorJetScalar parameters length compact state row component radial 1 r mode)) polar := by
  have derivative := ((Grad.AnnularOrbitGenerators.cellExponential_hasDerivAt mode.1 polar).mul_const
    (radialCofactorJetScalar parameters length compact state row component radial 0 r mode)).const_mul (cellExponential mode.2 axial)
  convert derivative using 1 <;> try rfl
  dsimp only [radialCofactorJetScalar,cofactorJetSequence,cofactorJetMultiplier]
  simp only [Fin.reduceEq,ite_true,ite_false,one_mul]
  ring

theorem originalCofactorTerm_axial (mode : ℤ × ℤ) (polar axial : ℝ) :
    HasDerivAt (fun angle => cellExponential mode.2 angle *
      (cellExponential mode.1 polar * radialCofactorJetScalar parameters length compact state row component radial 0 r mode))
      (cellExponential mode.2 axial * (cellExponential mode.1 polar *
        radialCofactorJetScalar parameters length compact state row component radial 2 r mode)) axial := by
  have derivative := (Grad.AnnularOrbitGenerators.cellExponential_hasDerivAt mode.2 axial).mul_const
    (cellExponential mode.1 polar * radialCofactorJetScalar parameters length compact state row component radial 0 r mode)
  convert derivative using 1 <;> try rfl
  dsimp only [radialCofactorJetScalar,cofactorJetSequence,cofactorJetMultiplier]
  simp only [Fin.reduceEq,ite_true,ite_false,one_mul]
  ring

/-- Literal original R coefficient, proved by the full convergent integer Fourier series. -/
theorem originalCofactorJetSeries_angular (polar axial : ℝ) :
    HasDerivAt (fun angle => originalCofactorJetSeries parameters length compact state row component radial 0 r (angle,axial))
      (originalCofactorJetSeries parameters length compact state row component radial 1 r (polar,axial)) polar := by
  exact hasDerivAt_tsum_of_isPreconnected
    (cofactorJetScalar_norm_summable parameters length compact state row component radial 1 r) isOpen_univ isPreconnected_univ
    (fun mode angle _ => originalCofactorTerm_angular parameters length compact state row component radial r mode angle axial)
    (fun mode angle _ => by simp only [norm_mul,cellExponential_norm,one_mul,le_refl]) (by simp : (0 : ℝ) ∈ (Set.univ : Set ℝ))
    (originalCofactorJetSeries_hasSum parameters length compact state row component radial 0 r (0,axial)).summable (by simp)

/-- Literal original axial coefficient derivative, without discarding any axial cell. -/
theorem originalCofactorJetSeries_axial (polar axial : ℝ) :
    HasDerivAt (fun angle => originalCofactorJetSeries parameters length compact state row component radial 0 r (polar,angle))
      (originalCofactorJetSeries parameters length compact state row component radial 2 r (polar,axial)) axial := by
  exact hasDerivAt_tsum_of_isPreconnected
    (cofactorJetScalar_norm_summable parameters length compact state row component radial 2 r) isOpen_univ isPreconnected_univ
    (fun mode angle _ => originalCofactorTerm_axial parameters length compact state row component radial r mode polar angle)
    (fun mode angle _ => by simp only [norm_mul,cellExponential_norm,one_mul,le_refl]) (by simp : (0 : ℝ) ∈ (Set.univ : Set ℝ))
    (originalCofactorJetSeries_hasSum parameters length compact state row component radial 0 r (polar,0)).summable (by simp)

end Grad.ActualPolarFlux
