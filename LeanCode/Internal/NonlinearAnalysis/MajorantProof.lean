import MajorantRootSummable
import MajorantExpSummable

/-!
# NG_F06: proof of the coefficient-series majorant goal

`actualCoefficientMajorant : CoefficientMajorantGoal` assembles the Q8
placement estimate and summability (`MajorantRootBound`,
`MajorantRootSummable`) and the N3 placement estimate, order-zero identity
and factorial summability (`MajorantExpBound`, `MajorantExpSummable`).
-/

noncomputable section

namespace Grad.CoefficientMajorants

/-- NG_F06 is proved. -/
theorem actualCoefficientMajorant : CoefficientMajorantGoal := by
  refine ⟨?_, ?_⟩
  · intro parameters grade order theta radius thetaNonneg thetaLt radiusNonneg
    refine ⟨rootOperatorMajorant_summable parameters grade order thetaNonneg thetaLt radiusNonneg,
      ?_⟩
    intro x lowBall highBall directions p
    exact rootDerivativeTerm_envelope_le grade order p thetaNonneg radiusNonneg lowBall highBall
      directions
  · intro L sigma gamma ell admissible grade dimension order radius radiusNonneg
    refine ⟨expOperatorMajorant_summable grade _ radius order,
      fun base p => exponentialDerivativeTerm_zero admissible base p, ?_⟩
    intro base baseLe directions p
    exact exponentialDerivativeTerm_norm_le admissible order p radiusNonneg baseLe
      directions

end Grad.CoefficientMajorants
