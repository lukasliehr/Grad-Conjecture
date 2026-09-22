import Showcase_DefinitionSurface
import Showcase_WithProofs
import Lean

open Lean Elab Command Meta

private def originalName (name : Name) : Name :=
  if (`Grad.ShowcaseSurface.MainTarget).isPrefixOf name then
    name.replacePrefix `Grad.ShowcaseSurface.MainTarget `Grad.MainTarget
  else if (`Grad.ShowcaseSurface.Public).isPrefixOf name then
    name.replacePrefix `Grad.ShowcaseSurface.Public `Grad.Showcase
  else name

private def originalExpr (e : Expr) : Expr :=
  let e := e.replace fun
    | .const name levels => some (.const (originalName name) levels)
    | _ => none
  e.replace fun
    | .proj name index value =>
      if originalName name == name then none
      else some (.proj (originalName name) index value)
    | _ => none

set_option maxHeartbeats 0 in
run_cmd do
  let names : Array Name := #[
    `Grad.MainTarget.Vec,
    `Grad.MainTarget.Plane,
    `Grad.MainTarget.PeriodicCircle,
    `Grad.MainTarget.ClosedDisk,
    `Grad.MainTarget.ReferenceDomain,
    `Grad.MainTarget.Torus,
    `Grad.MainTarget.vector,
    `Grad.MainTarget.planarPart,
    `Grad.MainTarget.cylinder,
    `Grad.MainTarget.fundamentalCylinder,
    `Grad.MainTarget.quotientPoint,
    `Grad.MainTarget.periodicLift,
    `Grad.MainTarget.Regularity,
    `Grad.MainTarget.Regularity.order,
    `Grad.MainTarget.Regularity.predecessor,
    `Grad.MainTarget.Regularity.admits,
    `Grad.MainTarget.HasLocalExtensions,
    `Grad.MainTarget.HasRegularity,
    `Grad.MainTarget.IsEmbeddingOfRegularity,
    `Grad.MainTarget.Representative,
    `Grad.MainTarget.IsConfiguration,
    `Grad.MainTarget.Configuration,
    `Grad.MainTarget.jets,
    `Grad.MainTarget.configurationTopology,
    `Grad.MainTarget.HasRegularLocalLifts,
    `Grad.MainTarget.IsReparametrization,
    `Grad.MainTarget.ModuliEquivalent,
    `Grad.MainTarget.ModuliSpace,
    `Grad.MainTarget.moduliClass,
    `Grad.MainTarget.moduliTopology,
    `Grad.MainTarget.basisVector,
    `Grad.MainTarget.gradient,
    `Grad.MainTarget.cross,
    `Grad.MainTarget.curl,
    `Grad.MainTarget.divergence,
    `Grad.MainTarget.SmoothNear,
    `Grad.MainTarget.TangentTo,
    `Grad.MainTarget.roundAxis,
    `Grad.MainTarget.rotation,
    `Grad.MainTarget.SignedStabilizes,
    `Grad.MainTarget.torusLift,
    `Grad.MainTarget.IsEmbeddedTorus,
    `Grad.MainTarget.pressureLevel,
    `Grad.MainTarget.IsRegularLevel,
    `Grad.MainTarget.FoliationDomain,
    `Grad.MainTarget.foliationCylinder,
    `Grad.MainTarget.foliationLift,
    `Grad.MainTarget.IsPressureFoliation,
    `Grad.MainTarget.SmoothFamily,
    `Grad.MainTarget.ModuliCurve,
    `Grad.Showcase.IsMHS,
    `Grad.Showcase.NestedPressureTori,
    `Grad.Showcase.ExactCyclicSymmetry,
    `Grad.Showcase.Equilibrium,
    `Grad.Showcase.same_moduli_class_iff,
    `Grad.Showcase.equilibria_with_exact_cyclic_symmetry]
  let names := names ++ #[`Grad.MainTarget.Regularity.finite,
    `Grad.MainTarget.Regularity.smooth, `Grad.MainTarget.Regularity.rec,
    `Grad.MainTarget.Representative.mk, `Grad.MainTarget.Representative.position,
    `Grad.MainTarget.Representative.magnetic, `Grad.MainTarget.Representative.pressure,
    `Grad.MainTarget.Representative.rec]
  liftTermElabM do
    let env ← getEnv
    for name in names do
      let surfaceName := if (`Grad.MainTarget).isPrefixOf name then
        name.replacePrefix `Grad.MainTarget `Grad.ShowcaseSurface.MainTarget
        else name.replacePrefix `Grad.Showcase `Grad.ShowcaseSurface.Public
      let some displayed := env.find? surfaceName | throwError "Missing surface: {surfaceName}"
      let some proved := env.find? name | throwError "Missing verified definition: {name}"
      unless ← withTransparency .all (isDefEq (originalExpr displayed.type) proved.type) do
        throwError "Declaration types differ: {name}"
      unless displayed.isTheorem do
        match displayed.value?, proved.value? with
        | some lhs, some rhs =>
          unless ← withTransparency .all (isDefEq (originalExpr lhs) rhs) do
            throwError "Definition values differ: {name}"
        | none, none => pure ()
        | _, _ => throwError "Declaration kinds differ: {name}"
    logInfo m!"SHOWCASE_ALL_DISPLAYED_DECLARATIONS_MATCH_VERIFIED {names.size}"
