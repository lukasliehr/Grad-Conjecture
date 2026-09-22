import AKAJ1ActualForceFourierSynthesis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualForceMatrixFidelity
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPhysicalAngular

open Grad.BoundaryKernelAction

def forceAngleEntry (parameters : PhaseParameters) (length epsilon : ℝ) (base : ACore parameters 3)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (angles : ℝ × ℝ) : ℂ :=
  forcePolarComponent kind angles.1 (originalForceMatrix parameters length epsilon base angles.2
    (polarClosedPoint radius angles.1 nonnegative bounded)) component

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (low : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (kind : Fin 2) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
include low

theorem forceAngleEntry_eq_tsum (component : Fin 3) (angles : ℝ × ℝ) :
    forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles =
      ∑' mode : ℤ × ℤ,cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 * forceScalar parameters length rho epsilon base kind low component 0 radius mode) :=
  (forceScalar_double_hasSum parameters length rho epsilon base low kind component radius nonnegative bounded angles.1 angles.2).tsum_eq.symm

theorem forceAngleEntry_continuous (component : Fin 3) : Continuous (forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded) := by
  rw [funext (forceAngleEntry_eq_tsum parameters length rho epsilon base low kind radius nonnegative bounded component)]
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp continuous_snd).mul
      (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul continuous_const))
    (forceScalar_norm_summable parameters length rho epsilon base low kind component radius nonnegative bounded)
  intro mode angles
  change ‖cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 * forceScalar parameters length rho epsilon base kind low component 0 radius mode)‖ ≤ _
  simp only [norm_mul,cellExponential_norm,one_mul,le_refl]

theorem forceAngleEntry_periodic (component : Fin 3) (angles : ℝ × ℝ) :
    forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded (angles.1+2*Real.pi,angles.2) = forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles ∧
    forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded (angles.1,angles.2+2*Real.pi) = forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles := by
  constructor <;> rw [forceAngleEntry_eq_tsum parameters length rho epsilon base low kind,forceAngleEntry_eq_tsum parameters length rho epsilon base low kind] <;>
    apply tsum_congr <;> intro mode <;> simp only [← cellCharacter_coe,AddCircle.coe_add_period]

theorem forceScalar_product_hasSum {dimension : ℕ} (component : Fin 3)
    (source : ℝ × ℝ → ComplexEuclidean dimension) (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => forceScalar parameters length rho epsilon base kind low component 0 radius shift • doubleCoefficient source (twoFrequencyTranslation shift mode))
      (doubleCoefficient (fun angles => forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles • source angles) mode) := by
  obtain ⟨bound,dominated⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi) continuousSource.continuousOn
  exact doubleCoefficient_series_product (forceScalar parameters length rho epsilon base kind low component 0 radius)
    (forceScalar_norm_summable parameters length rho epsilon base low kind component radius nonnegative bounded) (forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded) source
    (fun cell polar => angularCoefficient (fun axial => source (polar,axial)) cell)
    (fun polar => continuousSource.comp (continuous_const.prodMk continuous_id))
    (fun cell => Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter source continuousSource cell)
    (fun _ _ => rfl) (max bound 0) (le_max_right _ _)
    (fun polar polarInside axial axialInside => (dominated (polar,axial) ⟨polarInside,axialInside⟩).trans (le_max_left _ _))
    (fun polar _ axial _ => forceScalar_double_hasSum parameters length rho epsilon base low kind component radius nonnegative bounded polar axial) mode

def forceMatrixProduct (source : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ∑ component : Fin 3, forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles • matrixUnit (0 : Fin 1) component (source angles)

theorem forceMatrixProduct_continuous (source : ℝ × ℝ → ComplexEuclidean 3) (continuousSource : Continuous source) :
    Continuous (forceMatrixProduct parameters length epsilon base kind radius nonnegative bounded source) :=
  continuous_finsetSum _ (fun component _ =>
    (forceAngleEntry_continuous parameters length rho epsilon base low kind radius nonnegative bounded component).smul
      ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource))

theorem forceMatrixProduct_hasSum (source : ℝ × ℝ → ComplexEuclidean 3)
    (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => rowMultiplicationEntry 3 (fun component => forceScalar parameters length rho epsilon base kind low component 0 radius) shift (twoFrequencyTranslation shift mode)
      (doubleCoefficient source (twoFrequencyTranslation shift mode)))
      (doubleCoefficient (forceMatrixProduct parameters length epsilon base kind radius nonnegative bounded source) mode) := by
  have each (component : Fin 3) := forceScalar_product_hasSum parameters length rho epsilon base low kind radius nonnegative bounded component
    (fun angles => matrixUnit (0 : Fin 1) component (source angles)) ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource) mode
  have summed := hasSum_sum (s := Finset.univ) (fun component (_ : component ∈ (Finset.univ : Finset (Fin 3))) => each component)
  have coefficients (shift : ℤ × ℤ) :
      (∑ component : Fin 3,forceScalar parameters length rho epsilon base kind low component 0 radius shift •
        doubleCoefficient (fun angles => matrixUnit (0 : Fin 1) component (source angles)) (twoFrequencyTranslation shift mode)) =
      rowMultiplicationEntry 3 (fun component => forceScalar parameters length rho epsilon base kind low component 0 radius) shift (twoFrequencyTranslation shift mode)
        (doubleCoefficient source (twoFrequencyTranslation shift mode)) := by
    simp only [doubleCoefficient_valueMap _ source continuousSource,rowMultiplicationEntry,sum_apply,smul_apply]
  have limits : (∑ component : Fin 3,doubleCoefficient
      (fun angles => forceAngleEntry parameters length epsilon base kind component radius nonnegative bounded angles • matrixUnit (0 : Fin 1) component (source angles)) mode) =
      doubleCoefficient (forceMatrixProduct parameters length epsilon base kind radius nonnegative bounded source) mode := by
    unfold forceMatrixProduct
    rw [doubleCoefficient_finset_sum]
    intro component
    exact (forceAngleEntry_continuous parameters length rho epsilon base low kind radius nonnegative bounded component).smul
      ((matrixUnit (0 : Fin 1) component).continuous.comp continuousSource)
  rw [limits] at summed
  exact summed.congr_fun (fun shift => (coefficients shift).symm)

end Grad.ActualForceMatrixFidelity
