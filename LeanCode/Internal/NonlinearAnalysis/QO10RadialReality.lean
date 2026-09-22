import QO9ProductReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality Grad.NonlinearRadial

variable {parameters : PhaseParameters}

theorem radialCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (radialCore parameters field) =
      radialCore parameters (cartesianCoreConjugation parameters field) := by
  apply acore_ext
  intro cell point
  change cartesianPhysicalConjugation dimension
    (radialIntervalValue 0 1 (field.val (-cell)) point.val) =
      radialIntervalValue 0 1 (closedJetConjugate (field.val (-cell))) point.val
  unfold radialIntervalValue
  have integrable : IntegrableOn
      (fun scale : ℝ => Real.negMulLog scale •
        smoothClosedExtension (field.val (-cell)) (scale • point.val)) (Icc 0 1) :=
    (Real.continuous_negMulLog.smul ((smoothClosedExtension_smooth (field.val (-cell))).continuous.comp
      (continuous_id.smul continuous_const))).continuousOn.integrableOn_Icc
  have commutation : cartesianPhysicalConjugation dimension
      (∫ scale in Icc (0 : ℝ) 1, Real.negMulLog scale •
        smoothClosedExtension (field.val (-cell)) (scale • point.val)) =
      ∫ scale in Icc (0 : ℝ) 1, cartesianPhysicalConjugation dimension
        (Real.negMulLog scale • smoothClosedExtension (field.val (-cell)) (scale • point.val)) :=
    ((cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm integrable).symm
  rw [commutation]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale scaleIn
  dsimp only
  rw [(cartesianPhysicalConjugation dimension).map_smul]
  congr 1
  let contracted := dilationPoint scale scaleIn.1 scaleIn.2 point
  change cartesianPhysicalConjugation dimension
    (smoothClosedExtension (field.val (-cell)) contracted.val) =
      smoothClosedExtension (closedJetConjugate (field.val (-cell))) contracted.val
  rw [smoothClosedExtension_value, smoothClosedExtension_value]
  rfl

theorem laplacianCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (laplacianCore parameters field) =
      laplacianCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (partialCore parameters 0 (partialCore parameters 0 field) +
      partialCore parameters 1 (partialCore parameters 1 field)) = _
  rw [map_add, partialCore_conjugate, partialCore_conjugate,
    partialCore_conjugate, partialCore_conjugate]
  rfl

theorem quotientDotCurried_conjugate (first second : ACore parameters 3) :
    cartesianCoreConjugation parameters (quotientDotCurried parameters first second) =
      quotientDotCurried parameters (cartesianCoreConjugation parameters first)
        (cartesianCoreConjugation parameters second) := by
  change cartesianCoreConjugation parameters
    (radialCore parameters (laplacianCore parameters (angularCore parameters 0
      (dotOperation parameters (eulerCore parameters first) (rotationCore parameters second))))) = _
  rw [radialCore_conjugate, laplacianCore_conjugate, angularCore_conjugate, neg_zero,
    dotOperation_conjugate, eulerCore_conjugate, rotationCore_conjugate]
  rfl

theorem constantCore_conjugate {dimension : ℕ} (vector : ComplexEuclidean dimension) :
    cartesianCoreConjugation parameters (constantCore parameters vector) =
      constantCore parameters (cartesianPhysicalConjugation dimension vector) := by
  apply acore_ext
  intro cell point
  by_cases zeroCell : cell = 0
  · subst cell
    change cartesianPhysicalConjugation dimension
      (((constantCore parameters vector).val 0).value point) = _
    rw [constantCore_value_zero, constantCore_value_zero]
  · change cartesianPhysicalConjugation dimension
      (((constantCore parameters vector).val (-cell)).value point) = _
    rw [constantCore_value_ne vector (neg_ne_zero.mpr zeroCell),
      constantCore_value_ne _ zeroCell, map_zero]

theorem scalarConstantCore_conjugate (scalar : ℂ) :
    cartesianCoreConjugation parameters (scalarConstantCore parameters scalar) =
      scalarConstantCore parameters (conj scalar) := by
  rw [scalarConstantCore, constantCore_conjugate]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [cartesianPhysicalConjugation]

end Grad.NonlinearRange
