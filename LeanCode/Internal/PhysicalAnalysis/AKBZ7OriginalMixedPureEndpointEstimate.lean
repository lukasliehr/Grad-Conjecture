import AKBZ6OriginalPureEndpointNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- CT6 on the literal original mixed norm. This sums the SAME weighted
field over every signed cell; it uses no cap phase or doubled running grade. -/
theorem originalMixedNorm_pureEndpoints {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 0<grade) (field : ACore parameters dimension) :
    originalGradeNorm grade field≤(2*apMassEndpointConstant 0 grade)*
      (originalPlanarNorm parameters grade field+originalCellNorm parameters grade field) := by
  let constant := apMassEndpointConstant 0 grade
  have constantNonnegative : 0≤constant := apMassEndpointConstant_nonnegative 0 grade
  have pointwise (cell : ℤ) :
      ‖cellGradeRowLinear (grade:=grade) parameters cell (field.val cell)‖^2≤
        (2*constant^2)*
          (((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖)^2+
            ‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖^2) := by
    rw [originalWeightedRow_mass]
    have bound := apMassRow_endpoints (cellFrequency cell) (cellFrequency_one_le cell) gradePositive
      (phaseWeightedJet parameters cell (field.val cell))
    simp only [Nat.sub_zero] at bound
    have square := pow_le_pow_left₀ (norm_nonneg _) bound 2
    have positive := mul_nonneg (sq_nonneg constant)
      (sq_nonneg ((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖-
        ‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖))
    dsimp only [constant] at *
    nlinarith only [square,positive]
  have cellSummable := originalCellNorm_summable parameters grade field
  have planarSummable := originalPlanarNorm_summable parameters grade field
  have sumBound := (original_rows_summable parameters field).tsum_le_tsum pointwise
    ((cellSummable.add planarSummable).mul_left (2*constant^2))
  rw [tsum_mul_left,cellSummable.tsum_add planarSummable,
    ←originalCellNorm_sq parameters grade field,←originalPlanarNorm_sq parameters grade field] at sumBound
  have original : originalGradeNorm grade field^2=
      ∑' cell : ℤ,‖cellGradeRowLinear (grade:=grade) parameters cell (field.val cell)‖^2 :=
    originalGrade_norm_sq_eq_rows parameters field
  rw [←original] at sumBound
  have planarNonnegative : 0≤originalPlanarNorm parameters grade field := Real.sqrt_nonneg _
  have cellNonnegative : 0≤originalCellNorm parameters grade field := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (originalGradeNorm_nonnegative grade field)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) constantNonnegative)
      (add_nonneg planarNonnegative cellNonnegative))).mp
  have mixedNonnegative := mul_nonneg (sq_nonneg constant)
    (mul_nonneg planarNonnegative cellNonnegative)
  nlinarith only [sumBound,mixedNonnegative,sq_nonneg (constant*originalPlanarNorm parameters grade field),
    sq_nonneg (constant*originalCellNorm parameters grade field)]

end Grad.OriginalCartesianTameEstimate
