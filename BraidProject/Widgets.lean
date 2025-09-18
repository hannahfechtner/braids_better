import BraidProject.BraidGroup
import ProofWidgets.Component.HtmlDisplay
import Lean.Widget

structure BraidProps where
  strands : Nat
  generators : List (Nat × Bool)
  deriving Lean.ToJson, Lean.FromJson

structure BraidCarousel where
  braids : List BraidProps
  idx : ℕ
deriving Lean.ToJson, Lean.FromJson

open ProofWidgets

@[widget_module]
def FixedBraidWidgetModule : Lean.Widget.Module where
  javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"
-- def FixedBraidWidget : Component BraidProps where
--   Lean.Widget.mkModule (include_str ".." / ".lake" / "build" / "js" / "braid.js") --javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"

def FixedBraidWidget : Component BraidProps where
  javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"

--specify which functin you want
@[widget_module]
def CarouselBraidWidgetModule : Lean.Widget.Module where
  javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"
-- def FixedBraidWidget : Component BraidProps where
--   Lean.Widget.mkModule (include_str ".." / ".lake" / "build" / "js" / "braid.js") --javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"

def CarouselBraidWidget : Component BraidCarousel where
  javascript := include_str ".." / ".lake" / "build" / "js" / "braid.js"

open scoped Jsx in
#html <FixedBraidWidget
  strands={6}
  generators={[
    (1, false), (2, true), (1, false), (0, true),
    (1, false), (0, true), (1, false), (0, true),
    (3, false), (2, false), (3, false), (4, true),
    (3, false), (4, true), (3, false), (0, true)
  ]} />

open scoped Jsx in
#html <CarouselBraidWidget
  braids={
    [
      { strands := 4, generators := [ (0, true), (1, false), (0, true), (0, false) ] },
      { strands := 5, generators := [ (2, false), (3, true), (1, true), (0, false) ] },
      { strands := 6, generators := [ (4, true), (1, false), (2, true), (3, true) ] }
    ]
  }
  idx={0}
/>

open Lean Meta in
unsafe def evalListNBoolUnsafe (e : Expr) : MetaM (List (ℕ × Bool)) :=
  evalExpr _
    (.app (.const ``List [0])
      (mkApp2 (.const ``Prod [0, 0])
       (.const ``Nat []) (.const ``Bool []))) e

open Lean Meta in
unsafe def evalListListNBoolUnsafe (e : Expr) : MetaM (List (List (ℕ × Bool))) :=
  evalExpr _
    (.app (.const ``List [0]) (.app (.const ``List [0])
      (mkApp2 (.const ``Prod [0, 0])
       (.const ``Nat []) (.const ``Bool [])))) e

open Lean Meta in
@[implemented_by evalListNBoolUnsafe]
opaque evalListNBool (e : Expr) : MetaM (List (ℕ × Bool))

open Lean Meta in
@[implemented_by evalListListNBoolUnsafe]
opaque evalListListNBool (e : Expr) : MetaM (List (List (ℕ × Bool)))


open Lean Meta in
partial def parseBraid (e : Expr) : MetaM (List (ℕ × Bool)) := do
  match_expr e with
  | List.nil _ => (evalListNBool e)
  | List.cons _ _ _ => (evalListNBool e)
  | HMul.hMul _ _ _ _ a b =>
    return (← parseBraid a) ++ (← parseBraid b)
  | Inv.inv _ _ k => do
    let l ← parseBraid k
    return FreeGroup.invRev l
  | Braid.σ n k => do
    -- btw, Quote4 is a library that makes producing Exprs easier
    let v ← whnf <| mkApp2 (.const ``Fin.val []) n k
    logInfo m!"{v}"
    let some k ← Meta.evalNat v
      | throwError "could not evaluate {v}"
    return [(k, true)]
  | _ =>
    if let .const _ _ := e then
      let e ← Meta.unfoldDefinition e
      return ← parseBraid e
    throwError "I do not know{indentExpr e}"

open Lean Meta in
partial def parseBraidStrands (e : Expr) : MetaM Nat := do
  match_expr e with
  | HMul.hMul _ _ _ _ a b =>
    return max (← parseBraidStrands a) (← parseBraidStrands b)
  | Inv.inv _ _ k => do
    return (← parseBraidStrands k)
  | Braid.σ n k => do
    -- btw, Quote4 is a library that makes producing Exprs easier
    let v ← whnf <| mkApp2 (.const ``Fin.val []) n k
    logInfo m!"{v}"
    let some k ← Meta.evalNat v
      | throwError "could not evaluate {v}"
    return k + 2 -- number of strands needed
  | _ =>
    if let .const _ _ := e then
      let e ← Meta.unfoldDefinition e
      return ← parseBraidStrands e
    throwError "I do not know{indentExpr e}"
-- open Lean Meta in
-- partial def parseWord (e : Expr) : MetaM (List (ℕ × Bool)) := do
--   match_expr e with
--   | List.cons _ a b =>
--     match_expr a with
--     | Prod.mk _ _ x y =>
--       let some k ← Meta.evalNat x
--         | throwError "could not evaluate {a}"
--       let bo ← Meta.evalBool y
--         --| throwError "could not evaluate {a}"
--       return [(k, bo)] ++ (← parseWord b)
--     | _ => throwError "could not evaluate {a}"
--   | List.nil _ => return []
--   | _ =>
--     if let .const _ _ := e then
--       let e ← Meta.unfoldDefinition e
--       return ← parseWord e
--     throwError "I do not know{indentExpr e}"

open Lean Elab in
elab stx:"#show_braid" t:term : command => do
  Command.liftTermElabM do
    --let n ← Meta.mkFreshExprMVar (mkConst ``Nat)
    --let gen ← Meta.mkFreshExprMVar (mkConst ``List)
    --let expectedTp := mkApp (mkConst ``Braid.BraidGroupFin) n
    let e ← Term.elabTerm t none

    let eTp ← Meta.inferType e
    let generators ← parseBraid e
    let n ←
      match_expr eTp with
      | Braid.BraidGroupFin n' =>
        let n? : Option Nat ← liftM $ Meta.evalNat n'

        -- TODO: fix error on `#show_braid (σ 0 * σ 1 : braid_group 2)`
        let some n := n? | throwError "unknown number {n'} of strings in {eTp}"
        pure n
      | List _ => pure <|
        match List.max? (List.map (fun x => x.1) generators) with
        | some n => n + 2
        | none => 1
      | _ => throwError "expected a braid group element, got {eTp}"
    --let e ← Term.ensureHasType expectedTp e
    -- filling in the `n` hole in expectedTp; eTp knows the type (has no holes)
    --let _ ← Meta.isDefEq eTp expectedTp
    --let gen? : Option (List (ℕ × Bool)) ← liftM $ Meta.evalExpr gen

    -- ... finish computing the generators
    Widget.savePanelWidgetInfo
      (hash FixedBraidWidget.javascript)
      (return json%{ strands: $(n), generators: $(generators) })
      stx

open Lean Elab in
elab stx:"#show_braid_bounded" t:term : command => do
  Command.liftTermElabM do
    let n ← Meta.mkFreshExprMVar (mkConst ``Nat)
    --let gen ← Meta.mkFreshExprMVar (mkConst ``List)
    let expectedTp := mkApp (mkConst ``Braid.BraidGroupFin) n
    let e ← Term.elabTerm t expectedTp
    let e ← Term.ensureHasType expectedTp e
    let eTp ← Meta.inferType e
    -- filling in the `n` hole in expectedTp; eTp knows the type (has no holes)
    let _ ← Meta.isDefEq eTp expectedTp
    --let gen? : Option (List (ℕ × Bool)) ← liftM $ Meta.evalExpr gen
    let n? : Option Nat ← liftM $ Meta.evalNat n
    -- TODO: fix error on `#show_braid (σ 0 * σ 1 : braid_group 2)`
    let some n := n? | throwError "unknown number {n} of strings in {eTp}"
    let e1 := e
    let strands ← parseBraidStrands e
    let generators ← parseBraid e1
    -- ... finish computing the generators
    Widget.savePanelWidgetInfo
      (hash CarouselBraidWidget.javascript)
      (return json%{ strands: $(strands), generators: $(generators)})
      stx

open Lean Elab in
elab stx:"#show_braid_word" t:term : command => do
  Command.liftTermElabM do
    -- let n ← Meta.mkFreshExprMVar (mkConst ``Nat)
    -- --let gen ← Meta.mkFreshExprMVar (mkConst ``List)
    let expectedTp := mkApp (mkConst ``List) (mkApp (mkConst ``List) (mkConst ``Nat))
    let e ← Term.elabTerm t expectedTp
    -- let e ← Term.ensureHasType expectedTp e
    -- let eTp ← Meta.inferType e
    -- -- filling in the `n` hole in expectedTp; eTp knows the type (has no holes)
    -- let _ ← Meta.isDefEq eTp expectedTp
    -- --let gen? : Option (List (ℕ × Bool)) ← liftM $ Meta.evalExpr gen
    -- let n? : Option Nat ← liftM $ Meta.evalNat n
    -- TODO: fix error on `#show_braid (σ 0 * σ 1 : braid_group 2)`
    --let some n := n? | throwError "unknown number {n} of strings in {eTp}"
    let generators ← evalListNBool e
    let strands := List.max? (List.map (fun x => x.1) generators)
    -- ... finish computing the generators
    Widget.savePanelWidgetInfo
      (hash CarouselBraidWidget.javascript)
      (return json%{ strands: $(match strands with
                                | some n => n + 2
                                | none => 1), generators: $(generators) })
      stx

/-- Compute the number of strands needed for a braid word.
    If the word is empty we default to 1; otherwise `max(i) + 2`. -/
def strandsFromGenerators (gens : List (Nat × Bool)) : Nat :=
  match gens with
  | []      => 1
  | _ :: _  =>
    let maxIdx := gens.foldl (fun acc p => Nat.max acc p.fst) 0
    maxIdx + 2

/-- Convert a list of braid words into `BraidProps` for the carousel. -/
def toBraidProps (words : List (List (Nat × Bool))) : List BraidProps :=
  let max_gen := (match (List.max? (List.map (fun x => x.1) (List.flatten words))) with
          | some n => n + 2
          | none => 1)
  words.map (fun gens => {generators := List.map (fun x => (x.1, !x.2)) gens, strands := max_gen})

open Lean Elab in
elab stx:"#show_braid_word_help" t:term : command => do
  Command.liftTermElabM do
    -- let n ← Meta.mkFreshExprMVar (mkConst ``Nat)
    -- --let gen ← Meta.mkFreshExprMVar (mkConst ``List)
    let expectedTp := mkApp (mkConst ``List) (mkApp (mkConst ``List)
        ((mkApp2 (.const ``Prod [0, 0])
       (.const ``Nat []) (.const ``Bool []))))
    let e ← Term.elabTerm t expectedTp
    -- let e ← Term.ensureHasType expectedTp e
    -- let eTp ← Meta.inferType e
    -- -- filling in the `n` hole in expectedTp; eTp knows the type (has no holes)
    -- let _ ← Meta.isDefEq eTp expectedTp
    -- --let gen? : Option (List (ℕ × Bool)) ← liftM $ Meta.evalExpr gen
    -- let n? : Option Nat ← liftM $ Meta.evalNat n
    -- TODO: fix error on `#show_braid (σ 0 * σ 1 : braid_group 2)`
    --let some n := n? | throwError "unknown number {n} of strings in {eTp}"
    let braids ← evalListListNBool e
    --let strands := List.max? (List.map (fun x => x.1) generators)
    -- ... finish computing the generators
    Widget.savePanelWidgetInfo
      (hash CarouselBraidWidget.javascript)
      (return json%{ braids: $(toBraidProps braids)})
      stx

open Braid

#show_braid_word_help ([[(3, true), (2, true), (0, false), (3, true)],
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))

--#show_braid_word [(3, false)]
#show_braid (σ (0 : Fin 4) * (σ (1 : Fin 4))⁻¹ * σ (0 : Fin 4) : BraidGroupFin 4)

def foo : BraidGroupFin 17 := σ 0 * (σ 1)⁻¹ * σ 0
#show_braid foo
#show_braid_bounded foo * foo * foo * foo⁻¹
#show_braid foo * foo
#show_braid (σ 2 : BraidGroupFin 4)⁻¹ * (σ 2 : BraidGroupFin 4)

-- ask on zulip about things like instantiating metavariables
-- add delta braids
-- infer type; case on type to remove the need for show_braid_word
-- add optConfig with a +bounded notation
-- javascript linear interpolation
