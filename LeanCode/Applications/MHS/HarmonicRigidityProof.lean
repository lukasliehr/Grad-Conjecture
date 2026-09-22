import HarmonicRigidity
import HarmonicRigidityInterface

noncomputable section

namespace Grad.MainAssembly.HarmonicRigidity

theorem piLatticeConstant : PiLatticeConstantGoal :=
  continuous_piLattice_constant

theorem harmonicNormalSign : HarmonicNormalSignGoal alphaAngle :=
  harmonic_normal_sign_and_lattice_zero

theorem firstHarmonicPeriod : FirstHarmonicPeriodGoal alphaAngle :=
  first_harmonic_forces_integral_period

theorem secondHarmonicRigidity : SecondHarmonicRigidityGoal alphaAngle :=
  ⟨second_harmonic_forces_parameter_and_tangent_sign,
    harmonic_congruence_of_fixed_data⟩

end Grad.MainAssembly.HarmonicRigidity
