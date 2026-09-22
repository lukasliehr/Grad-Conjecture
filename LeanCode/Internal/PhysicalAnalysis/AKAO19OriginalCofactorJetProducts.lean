import AKAO18LiteralPolarAngularJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (r : RadialPoint)

theorem originalCofactorJetSeries_product_hasSum {dimension : ℕ} (component : Fin 3)
    (source : ℝ × ℝ → ComplexEuclidean dimension) (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => radialCofactorJetScalar parameters length compact state row component radial direction r shift •
      doubleCoefficient source (twoFrequencyTranslation shift mode))
      (doubleCoefficient (fun angles => originalCofactorJetSeries parameters length compact state row component radial direction r angles • source angles) mode) := by
  obtain ⟨bound,dominated⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi) continuousSource.continuousOn
  exact doubleCoefficient_series_product (radialCofactorJetScalar parameters length compact state row component radial direction r)
    (cofactorJetScalar_norm_summable parameters length compact state row component radial direction r)
    (originalCofactorJetSeries parameters length compact state row component radial direction r) source
    (fun cell polar => angularCoefficient (fun axial => source (polar,axial)) cell)
    (fun polar => continuousSource.comp (continuous_const.prodMk continuous_id))
    (fun cell => Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter source continuousSource cell)
    (fun _ _ => rfl) (max bound 0) (le_max_right _ _)
    (fun polar polarInside axial axialInside => (dominated (polar,axial) ⟨polarInside,axialInside⟩).trans (le_max_left _ _))
    (fun polar _ axial _ => originalCofactorJetSeries_hasSum parameters length compact state row component radial direction r (polar,axial)) mode

def originalCofactorJetRowProduct (source : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ∑ component : Fin 3,originalCofactorJetSeries parameters length compact state row component radial direction r angles •
    matrixUnit (0 : Fin 1) component (source angles)

theorem originalCofactorJetRowProduct_continuous (source : ℝ × ℝ → ComplexEuclidean 3) (continuousSource : Continuous source) :
    Continuous (originalCofactorJetRowProduct parameters length compact state row radial direction r source) :=
  continuous_finsetSum _ (fun component _ =>
    (originalCofactorJetSeries_continuous parameters length compact state row component radial direction r).smul
      ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource))

theorem originalCofactorJetRowProduct_hasSum (source : ℝ × ℝ → ComplexEuclidean 3)
    (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => rowMultiplicationEntry 3
      (fun component => radialCofactorJetScalar parameters length compact state row component radial direction r)
      shift (twoFrequencyTranslation shift mode) (doubleCoefficient source (twoFrequencyTranslation shift mode)))
      (doubleCoefficient (originalCofactorJetRowProduct parameters length compact state row radial direction r source) mode) := by
  have each (component : Fin 3) := originalCofactorJetSeries_product_hasSum parameters length compact state row radial direction r component
    (fun angles => matrixUnit (0 : Fin 1) component (source angles)) ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource) mode
  have summed := hasSum_sum (s := Finset.univ) (fun component (_ : component ∈ (Finset.univ : Finset (Fin 3))) => each component)
  have coefficients (shift : ℤ × ℤ) :
      (∑ component : Fin 3,radialCofactorJetScalar parameters length compact state row component radial direction r shift •
        doubleCoefficient (fun angles => matrixUnit (0 : Fin 1) component (source angles)) (twoFrequencyTranslation shift mode)) =
      rowMultiplicationEntry 3 (fun component => radialCofactorJetScalar parameters length compact state row component radial direction r)
        shift (twoFrequencyTranslation shift mode) (doubleCoefficient source (twoFrequencyTranslation shift mode)) := by
    simp only [doubleCoefficient_valueMap _ source continuousSource,rowMultiplicationEntry,sum_apply,smul_apply]
  have limits : (∑ component : Fin 3,doubleCoefficient
      (fun angles => originalCofactorJetSeries parameters length compact state row component radial direction r angles • matrixUnit (0 : Fin 1) component (source angles)) mode) =
      doubleCoefficient (originalCofactorJetRowProduct parameters length compact state row radial direction r source) mode := by
    unfold originalCofactorJetRowProduct
    rw [doubleCoefficient_finset_sum]
    intro component
    exact (originalCofactorJetSeries_continuous parameters length compact state row component radial direction r).smul
      ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource)
  rw [limits] at summed
  exact summed.congr_fun (fun shift => (coefficients shift).symm)

end Grad.ActualPolarFlux
