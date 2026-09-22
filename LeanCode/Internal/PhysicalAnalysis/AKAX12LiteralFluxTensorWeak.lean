import AKAX11LiteralForceScalarTensorWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets

theorem startupFinitePrincipalSplit (principal : Fin 2 → ℂ) (rows : Fin 2 → Fin 2 → ℂ) :
    (∑ inner : Fin 2, (principal inner - (2 : ℂ) • ∑ middle : Fin 2, rows inner middle)) =
      (∑ inner : Fin 2, principal inner) - (2 : ℂ) • ∑ middle : Fin 2, ∑ inner : Fin 2, rows inner middle := by
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_comm]

/-- The literal s-row is div(s) minus twice the rotated true inverse term.
 No radial-mean correction is silently removed from s. -/
theorem startupPrincipalFlux_mixedWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) (outer : Fin 2) :
    (∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupPrincipalFixedKernel outer inner 2 field)) =
      (∑ inner : Fin 2, startupTestPairing cell ((startupPlanarEntryMap outer inner).adjoint vector)
        (startupDerivativeTest inner (startupDerivativeTest outer test)) field) -
      (2 : ℂ) • ∑ middle : Fin 2,
        startupTestPairing cell ((startupPlanarRotatedEntryMap outer middle).adjoint vector)
          (startupDerivativeTest middle (startupTrueInverseTest (startupDerivativeTest outer test))) field := by
  calc
    _ = ∑ inner : Fin 2,
        (startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
          (originalValueKernel (startupPlanarEntryMap outer inner) field) -
        (2 : ℂ) • ∑ middle : Fin 2,
          startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
            (originalValueKernel (startupPlanarRotatedEntryMap outer middle)
              (startupTrueInverseTensorKernel middle inner field))) := by
      apply Finset.sum_congr rfl
      intro inner _
      change startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
        (originalValueKernel (startupPlanarEntryMap outer inner) field -
          (2 : ℂ) • (∑ middle : Fin 2, (originalValueKernel (startupPlanarRotatedEntryMap outer middle)).comp
            (startupTrueInverseTensorKernel middle inner)) field) = _
      simp only [map_sub, map_smul, sum_apply, map_sum, ContinuousLinearMap.comp_apply]
    _ = (∑ inner : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest inner (startupDerivativeTest outer test))
        (originalValueKernel (startupPlanarEntryMap outer inner) field)) -
        (2 : ℂ) • ∑ middle : Fin 2, ∑ inner : Fin 2,
          startupTestPairing cell vector (startupDerivativeTest inner (startupDerivativeTest outer test))
            (originalValueKernel (startupPlanarRotatedEntryMap outer middle)
              (startupTrueInverseTensorKernel middle inner field)) := startupFinitePrincipalSplit _ _
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro inner _
        exact congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing field)
          (startupTestPairing_valueMap (startupPlanarEntryMap outer inner) cell vector
            (startupDerivativeTest inner (startupDerivativeTest outer test)))
      · congr 1
        apply Finset.sum_congr rfl
        intro middle _
        exact (startupValueTensor_mixedWeak (startupPlanarRotatedEntryMap outer middle)
          cell vector test field outer middle).symm

end Grad.CartesianStartup
