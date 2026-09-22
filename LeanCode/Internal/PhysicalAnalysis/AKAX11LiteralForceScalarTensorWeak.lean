import AKAX10ValueMapWeakTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Both literal curl signs in the principal a-row, now as an exact weak identity. -/
theorem startupPrincipalForce_mixedWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) (outer : Fin 2) :
    (∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupPrincipalFixedKernel outer inner 0 field)) =
      startupTestPairing cell ((startupPlanarRotatedEntryMap outer 1).adjoint vector)
        (startupDerivativeTest 0 (startupTrueInverseTest (startupDerivativeTest outer test))) field -
      startupTestPairing cell ((startupPlanarRotatedEntryMap outer 0).adjoint vector)
        (startupDerivativeTest 1 (startupTrueInverseTest (startupDerivativeTest outer test))) field := by
  calc
    _ = ∑ inner : Fin 2,
        (startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
          (originalValueKernel (startupPlanarRotatedEntryMap outer 1) (startupTrueInverseTensorKernel 0 inner field)) -
        startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
          (originalValueKernel (startupPlanarRotatedEntryMap outer 0) (startupTrueInverseTensorKernel 1 inner field))) := by
      apply Finset.sum_congr rfl
      intro inner _
      change (startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))) (_ - _) = _
      exact map_sub _ _ _
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← startupValueTensor_mixedWeak, ← startupValueTensor_mixedWeak]

/-- The scalar principal tensor is exactly diagonal and retains the actual true inverse. -/
theorem startupPrincipalScalar_mixedWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) (outer : Fin 2) :
    (∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupPrincipalFixedKernel outer inner 1 field)) =
      startupTestPairing cell vector
        (startupTrueInverseTest (startupDerivativeTest outer (startupDerivativeTest outer test))) field := by
  calc
    _ = startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest outer test))
        (startupPrincipalFixedKernel outer outer 1 field) := by
      apply Finset.sum_eq_single outer
      · intro inner _ different
        have unequal : outer ≠ inner := Ne.symm different
        change startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
          ((if outer = inner then startupTrueAngularInverse 3 0 else 0) field) = 0
        rw [if_neg unequal, zero_apply, map_zero]
      · intro impossible
        exact (impossible (Finset.mem_univ outer)).elim
    _ = _ := by
      change startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest outer test))
        ((if outer = outer then startupTrueAngularInverse 3 0 else 0) field) = _
      rw [if_pos rfl]
      exact congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing field)
        (startupTestPairing_trueInverse cell vector (startupDerivativeTest outer (startupDerivativeTest outer test)))

end Grad.CartesianStartup
