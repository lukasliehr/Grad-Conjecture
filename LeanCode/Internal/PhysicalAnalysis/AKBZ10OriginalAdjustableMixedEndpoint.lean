import AKBZ9OriginalMixedOrderNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- CT7 in the literal full-cell original norm. The small epsilon is chosen
after the grade and does not shrink the physical coefficient neighborhood. -/
theorem originalMixedOrder_adjustable
    (grade order : ℕ) (orderPositive : 0<order) (orderTop : order<grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧ ∀ (dimension : ℕ) (parameters : PhaseParameters)
      (field : ACore parameters dimension),
      originalMixedOrderNorm parameters grade order field≤epsilon*originalPlanarNorm parameters grade field+
        remainder*originalCellNorm parameters grade field := by
  obtain ⟨remainder,nonnegative,bound⟩ := ordinaryMassOrder_adjustable grade order orderPositive orderTop
    (epsilon/2) (by positivity)
  refine ⟨2*remainder,mul_nonneg (by norm_num) nonnegative,?_⟩
  intro dimension parameters field
  have pointwise (cell : ℤ) :
      ((cellFrequency cell)^(grade-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell (field.val cell))‖)^2≤
        (2*(epsilon/2)^2)*‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖^2+
        (2*remainder^2)*
          ((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖)^2 := by
    have inequality := bound dimension (cellFrequency cell) (cellFrequency_one_le cell)
      (phaseWeightedJet parameters cell (field.val cell))
    have square := pow_le_pow_left₀ (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)) inequality 2
    have positive := sq_nonneg ((epsilon/2)*‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖-
      remainder*((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖))
    nlinarith only [square,positive]
  have planarSummable := (originalPlanarNorm_summable parameters grade field).mul_left (2*(epsilon/2)^2)
  have cellSummable := (originalCellNorm_summable parameters grade field).mul_left (2*remainder^2)
  have sumBound := (originalMixedOrderNorm_summable parameters grade order orderTop.le field).tsum_le_tsum pointwise
    (planarSummable.add cellSummable)
  rw [planarSummable.tsum_add cellSummable,tsum_mul_left,tsum_mul_left,
    ←originalPlanarNorm_sq parameters grade field,←originalCellNorm_sq parameters grade field,
    ←originalMixedOrderNorm_sq parameters grade order field] at sumBound
  have planarNonnegative : 0≤originalPlanarNorm parameters grade field := Real.sqrt_nonneg _
  have cellNonnegative : 0≤originalCellNorm parameters grade field := Real.sqrt_nonneg _
  have mixedNonnegative : 0≤originalMixedOrderNorm parameters grade order field := Real.sqrt_nonneg _
  apply (sq_le_sq₀ mixedNonnegative
    (add_nonneg (mul_nonneg epsilonPositive.le planarNonnegative)
      (mul_nonneg (mul_nonneg (by norm_num) nonnegative) cellNonnegative))).mp
  have cross := mul_nonneg (mul_nonneg epsilonPositive.le nonnegative) (mul_nonneg planarNonnegative cellNonnegative)
  nlinarith only [sumBound,cross,sq_nonneg (epsilon*originalPlanarNorm parameters grade field),
    sq_nonneg (remainder*originalCellNorm parameters grade field)]

end Grad.OriginalCartesianTameEstimate
