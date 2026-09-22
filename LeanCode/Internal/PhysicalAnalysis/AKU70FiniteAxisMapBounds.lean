import AKU69ScalarLiftSourcePayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation

theorem componentValue_bound_one {dimension : ℕ} (component : Fin dimension) :
    ‖componentValue dimension component‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simpa [componentValue,norm_smul] using (PiLp.norm_apply_le value component)

theorem axisComponent_bound {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (component : Fin dimension) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (axisComponent component data)‖ ≤
      ‖Grad.AxisCore.axisEta parameters dimension grade data‖ := by
  exact (axisValueMap_bound (componentValue dimension component) data grade).trans
    (mul_le_of_le_one_left (norm_nonneg _) (componentValue_bound_one component))

theorem scalarAxisPairFirst_bound_one : ‖scalarAxisPairFirst‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simp [scalarAxisPairFirst,PiLp.norm_eq_of_L2]

theorem scalarAxisPairSecond_bound_one : ‖scalarAxisPairSecond‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simp [scalarAxisPairSecond,PiLp.norm_eq_of_L2]

theorem scalarAxisPair_bound {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 1) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (scalarAxisPair first second)‖ ≤
      ‖Grad.AxisCore.axisEta parameters 1 grade first‖+‖Grad.AxisCore.axisEta parameters 1 grade second‖ := by
  rw [scalarAxisPair,map_add]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((axisValueMap_bound scalarAxisPairFirst first grade).trans
      (mul_le_of_le_one_left (norm_nonneg _) scalarAxisPairFirst_bound_one))
    ((axisValueMap_bound scalarAxisPairSecond second grade).trans
      (mul_le_of_le_one_left (norm_nonneg _) scalarAxisPairSecond_bound_one))

theorem finiteQuarterValue_bound_one : ‖quarterValueMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  exact (quarterValue_norm value).le.trans_eq (one_mul _).symm

theorem quadraticAxisPlanarOperator_bound {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (grade : ℕ) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (bounded : ∀ index, ‖Grad.AxisCore.axisEta parameters 2 grade (data index)‖ ≤ budget) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (quadraticAxisPlanarOperator data index)‖ ≤ 5*budget := by
  have turned (slot : Fin 3) : ‖Grad.AxisCore.axisEta parameters 2 grade (axisValueMap quarterValueMap (data slot))‖ ≤ budget :=
    (axisValueMap_bound quarterValueMap (data slot) grade).trans
      ((mul_le_of_le_one_left (norm_nonneg _) finiteQuarterValue_bound_one).trans (bounded slot))
  have rotation : ‖Grad.AxisCore.axisEta parameters 2 grade ((2 : ℂ) • data 2-(2 : ℂ) • data 0)‖ ≤ 4*budget := by
    rw [map_sub,map_smul,map_smul]
    have triangle := norm_sub_le ((2 : ℂ) • Grad.AxisCore.axisEta parameters 2 grade (data 2))
      ((2 : ℂ) • Grad.AxisCore.axisEta parameters 2 grade (data 0))
    norm_num only [norm_smul,Complex.norm_ofNat] at triangle
    nlinarith only [triangle,bounded 2,bounded 0]
  fin_cases index
  · change ‖Grad.AxisCore.axisEta parameters 2 grade (data 1+axisValueMap quarterValueMap (data 0))‖ ≤ _
    rw [map_add]
    have sum := (norm_add_le _ _).trans (add_le_add (bounded 1) (turned 0))
    linarith
  · change ‖Grad.AxisCore.axisEta parameters 2 grade (((2 : ℂ) • data 2-(2 : ℂ) • data 0)+axisValueMap quarterValueMap (data 1))‖ ≤ _
    rw [map_add]
    exact (norm_add_le _ _).trans ((add_le_add rotation (turned 1)).trans_eq (by ring))
  · change ‖Grad.AxisCore.axisEta parameters 2 grade (-data 1+axisValueMap quarterValueMap (data 2))‖ ≤ _
    rw [map_add,map_neg]
    have sum := norm_add_le (-Grad.AxisCore.axisEta parameters 2 grade (data 1))
      (Grad.AxisCore.axisEta parameters 2 grade (axisValueMap quarterValueMap (data 2)))
    rw [norm_neg] at sum
    linarith [bounded 1,turned 2]

theorem quadraticAxisPlanarInverse_bound {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (grade : ℕ) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (bounded : ∀ index, ‖Grad.AxisCore.axisEta parameters 2 grade (data index)‖ ≤ budget) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (quadraticAxisPlanarInverse data index)‖ ≤ 20*budget := by
  have first := quadraticAxisPlanarOperator_bound data grade budget nonnegative bounded
  have second := quadraticAxisPlanarOperator_bound (quadraticAxisPlanarOperator data) grade (5*budget) (by positivity) first
  have third := quadraticAxisPlanarOperator_bound (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator data)) grade (5*(5*budget)) (by positivity) second
  change ‖Grad.AxisCore.axisEta parameters 2 grade (-(1/9 : ℂ) •
    (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator data)) index+
      (10 : ℂ) • quadraticAxisPlanarOperator data index))‖ ≤ _
  rw [map_smul,norm_smul,map_add,map_smul]
  have triangle := norm_add_le
    (Grad.AxisCore.axisEta parameters 2 grade (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator data)) index))
    ((10 : ℂ) • Grad.AxisCore.axisEta parameters 2 grade (quadraticAxisPlanarOperator data index))
  norm_num only [norm_smul,Complex.norm_ofNat] at triangle
  norm_num
  nlinarith only [triangle,third index,first index,nonnegative]

theorem axisQuadraticDivergence_bound {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (grade : ℕ) (budget : ℝ)
    (bounded : ∀ index, ‖Grad.AxisCore.axisEta parameters 2 grade (data index)‖ ≤ budget) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (axisQuadraticDivergence data)‖ ≤ 6*budget := by
  have component (index : Fin 3) (direction : Fin 2) := (axisComponent_bound (data index) direction grade).trans (bounded index)
  apply (scalarAxisPair_bound _ _ grade).trans
  have first := norm_add_le ((2 : ℂ) • Grad.AxisCore.axisEta parameters 1 grade (axisComponent 0 (data 0)))
    (Grad.AxisCore.axisEta parameters 1 grade (axisComponent 1 (data 1)))
  have second := norm_add_le (Grad.AxisCore.axisEta parameters 1 grade (axisComponent 0 (data 1)))
    ((2 : ℂ) • Grad.AxisCore.axisEta parameters 1 grade (axisComponent 1 (data 2)))
  simp only [map_add,map_smul]
  norm_num only [norm_smul,Complex.norm_ofNat] at first second
  nlinarith only [first,second,component 0 0,component 1 1,component 1 0,component 2 1]

end Grad.FinitePhysicalJetLift
