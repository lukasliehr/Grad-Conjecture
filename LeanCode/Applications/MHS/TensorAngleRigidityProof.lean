import TensorAngleRigidity
import TensorAngleRigidityInterface

noncomputable section

namespace Grad.MainAssembly.TensorAngleRigidity

/-- Closed exact proof of `NG_R06`. -/
theorem tensorAngleCongruence :
    TensorAngleCongruenceGoal normalizedShape normalSignMatrix :=
  ⟨normalizedShape_eq_iff_piLattice, normalSign_conjugation⟩

end Grad.MainAssembly.TensorAngleRigidity
