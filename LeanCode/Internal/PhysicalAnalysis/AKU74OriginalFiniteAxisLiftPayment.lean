import AKU73OriginalCubicTargetPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Algebra Grad.ExhaustionSourceAllocation

def finiteEllBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  finiteActionBound parameters (originalCubicInverseAxisBound parameters length) (finiteCubicTargetBound parameters length)

def finitePlanarLiftBound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  4*finiteEllBound parameters length grade+20*finiteSourceAxisConstant grade

def finiteCovectorLiftBound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  axisCovectorConstant*(finitePlanarLiftBound parameters length grade+originalC2AxisBound length grade)

def finitePhysicalULiftBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  finiteActionBound parameters (originalInverseTransposeAxisBound parameters length) (finiteCovectorLiftBound parameters length)

def finiteS3LiftBound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  finiteEllBound parameters length grade+3*finitePlanarLiftBound parameters length grade

theorem finiteEllBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finiteEllBound parameters length grade :=
  finiteActionBound_nonnegative parameters _ _ (originalCubicInverseAxisBound_nonnegative parameters length)
    (finiteCubicTargetBound_nonnegative parameters length rho epsilon field low) grade

theorem finitePlanarLiftBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finitePlanarLiftBound parameters length grade :=
  add_nonneg (mul_nonneg (by norm_num) (finiteEllBound_nonnegative parameters length rho epsilon field low grade))
    (mul_nonneg (by norm_num) (finiteSourceAxisConstant_nonnegative grade))

theorem finiteCovectorLiftBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finiteCovectorLiftBound parameters length grade :=
  mul_nonneg axisCovectorConstant_nonnegative (add_nonneg (finitePlanarLiftBound_nonnegative parameters length rho epsilon field low grade)
    (originalC2AxisBound_nonnegative length grade))

theorem finitePhysicalULiftBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finitePhysicalULiftBound parameters length grade :=
  finiteActionBound_nonnegative parameters _ _ (originalInverseTransposeAxisBound_nonnegative parameters length rho epsilon field low)
    (finiteCovectorLiftBound_nonnegative parameters length rho epsilon field low) grade

theorem finiteS3LiftBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finiteS3LiftBound parameters length grade :=
  add_nonneg (finiteEllBound_nonnegative parameters length rho epsilon field low grade)
    (mul_nonneg (by norm_num) (finitePlanarLiftBound_nonnegative parameters length rho epsilon field low grade))

theorem originalLiftEllAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalLiftEllAxis parameters length rho epsilon field low source)‖ ≤
      finiteEllBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade :=
  axisFamilyAction_source_payment _ _ (originalCubicInverseAxisBound parameters length) (finiteCubicTargetBound parameters length)
    (originalCubicInverseAxisBound_nonnegative parameters length) (finiteCubicTargetBound_nonnegative parameters length rho epsilon field low)
    (originalCubicInverseAxisFamily_bound parameters length rho epsilon field low) (originalLiftAxis_low_four parameters length rho epsilon field low)
    source _ (originalCubicTargetAxis_payment parameters length rho epsilon field low source) grade

theorem originalLiftPlanarAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalLiftPlanarAxis parameters length rho epsilon field low source index)‖ ≤
      finitePlanarLiftBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have complement := (axisCubicComplementVector_bound
    (originalLiftEllAxis parameters length rho epsilon field low source) grade index).trans
    (mul_le_mul_of_nonneg_left (originalLiftEllAxis_payment parameters length rho epsilon field low source grade) (by norm_num : (0 : ℝ) ≤ 4))
  have force := quadraticAxisPlanarInverse_bound (originalForce2Axis source) grade
    (finiteSourceAxisConstant grade*finiteLiftAxisPayment parameters field rho epsilon source grade)
    (mul_nonneg (finiteSourceAxisConstant_nonnegative grade) (finiteLiftAxisPayment_nonnegative parameters field rho epsilon source grade))
    (originalForce2Axis_payment parameters field rho epsilon source grade) index
  change ‖Grad.AxisCore.axisEta parameters 2 grade (_-_)‖ ≤ _
  rw [map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add complement force).trans_eq (by unfold finitePlanarLiftBound; ring))

theorem originalLiftCovectorAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 3 grade (axisCovectorTriple
      (originalLiftPlanarAxis parameters length rho epsilon field low source index) (originalC2Axis length source index))‖ ≤
      finiteCovectorLiftBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  apply (axisCovectorTriple_bound _ _ grade).trans
  exact (mul_le_mul_of_nonneg_left (add_le_add
    (originalLiftPlanarAxis_payment parameters length rho epsilon field low source grade index)
    (originalC2Axis_payment parameters field rho epsilon length source grade index)) axisCovectorConstant_nonnegative).trans_eq (by
      unfold finiteCovectorLiftBound
      ring)

theorem originalLiftPhysicalUAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 3 grade (originalLiftPhysicalUAxis parameters length rho epsilon field low source index)‖ ≤
      finitePhysicalULiftBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade :=
  axisFamilyAction_source_payment _ _ (originalInverseTransposeAxisBound parameters length) (finiteCovectorLiftBound parameters length)
    (originalInverseTransposeAxisBound_nonnegative parameters length rho epsilon field low) (finiteCovectorLiftBound_nonnegative parameters length rho epsilon field low)
    (originalInverseTransposeAxisFamily_bound parameters length rho epsilon field low) (originalLiftAxis_low_four parameters length rho epsilon field low)
    source _ (fun indexGrade => originalLiftCovectorAxis_payment parameters length rho epsilon field low source indexGrade index) grade

theorem originalLiftS3Axis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 4) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalLiftS3Axis parameters length rho epsilon field low source index)‖ ≤
      finiteS3LiftBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have ell (component : Fin 2) := (axisComponent_bound
    (originalLiftEllAxis parameters length rho epsilon field low source) component grade).trans
    (originalLiftEllAxis_payment parameters length rho epsilon field low source grade)
  have planar (slot : Fin 3) (component : Fin 2) := (axisComponent_bound
    (originalLiftPlanarAxis parameters length rho epsilon field low source slot) component grade).trans
    (originalLiftPlanarAxis_payment parameters length rho epsilon field low source grade slot)
  have nonnegative := mul_nonneg (finitePlanarLiftBound_nonnegative parameters length rho epsilon field low grade)
    (finiteLiftAxisPayment_nonnegative parameters field rho epsilon source grade)
  fin_cases index
  · change ‖Grad.AxisCore.axisEta parameters 1 grade (_+_)‖ ≤ _
    rw [map_add]
    have sum := (norm_add_le _ _).trans (add_le_add (ell 0) (planar 0 1))
    unfold finiteS3LiftBound
    nlinarith only [sum,nonnegative]
  · change ‖Grad.AxisCore.axisEta parameters 1 grade ((_+_)-_)‖ ≤ _
    rw [map_sub,map_add]
    have sum := (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (ell 1) (planar 1 1))) (planar 0 0))
    unfold finiteS3LiftBound
    nlinarith only [sum,nonnegative]
  · change ‖Grad.AxisCore.axisEta parameters 1 grade ((_+_)-_)‖ ≤ _
    rw [map_sub,map_add]
    have sum := (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (ell 0) (planar 2 1))) (planar 1 0))
    unfold finiteS3LiftBound
    nlinarith only [sum,nonnegative]
  · change ‖Grad.AxisCore.axisEta parameters 1 grade (_-_)‖ ≤ _
    rw [map_sub]
    have sum := (norm_sub_le _ _).trans (add_le_add (ell 1) (planar 2 0))
    unfold finiteS3LiftBound
    nlinarith only [sum,nonnegative]

end Grad.FinitePhysicalJetLift
