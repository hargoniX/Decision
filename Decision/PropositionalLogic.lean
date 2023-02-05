import Lean
import Mathlib.Data.Bool.Basic

open Lean Parser Tactic

namespace Decision.Propositional

inductive Atom where
| ident (name : String)
| true
| false

inductive Formula where
| and (lhs rhs : Formula)
| or (lhs rhs : Formula)
| neg (f : Formula)
| atom (a : Atom)

declare_syntax_cat propositional

syntax "⊤" : propositional
syntax "⊥" : propositional
syntax ident : propositional

syntax:35 propositional " ∧ " propositional : propositional
syntax:30 propositional " ∨ " propositional : propositional
syntax:max "¬" propositional:40 : propositional
syntax "(" propositional ")" : propositional
syntax propositional " → " propositional : propositional

syntax "[prop|" propositional "]" : term
syntax "[t|" term "]" : propositional


macro_rules
| `([prop| ⊤]) => `(Formula.atom Atom.true)
| `([prop| ⊥]) => `(Formula.atom Atom.false)
| `([prop| $ident:ident]) => `(Formula.atom (Atom.ident $(Lean.quote ident.getId.toString)))
| `([prop| $lhs ∧ $rhs]) => `(Formula.and [prop| $lhs] [prop| $rhs])
| `([prop| $lhs ∨ $rhs]) => `(Formula.or [prop| $lhs] [prop| $rhs])
| `([prop| ¬$f]) => `(Formula.neg [prop| $f])
| `([prop| ($f)]) => `([prop| $f])
| `([prop| $lhs → $rhs]) => `([prop| ¬$lhs ∨ $rhs])
| `([prop| [t| $term]]) => `($term)

/--
Definition 1.1
-/
abbrev Assignment := String → Bool

def Atom.eval (assign : Assignment) : Atom → Bool
| .ident name => assign name
| .true => .true
| .false => .false

namespace Formula

def eval (assign : Assignment) : Formula → Bool
| .and lhs rhs => eval assign lhs && eval assign rhs
| .or lhs rhs => eval assign lhs || eval assign rhs
| .neg f => !eval assign f
| .atom a => Atom.eval assign a

/--
Definition 1.2
-/
def IsSatisfiable (f : Formula) : Prop := ∃ assign : Assignment, f.eval assign = true

/--
Definition 1.2
-/
def IsContradiction (f : Formula) : Prop := ∀ assign : Assignment, f.eval assign = false

/--
Definition 1.2
-/
def IsValid (f : Formula) : Prop := ∀ assign : Assignment, f.eval assign = true

/--
Example 1.3
-/
example : IsSatisfiable [prop| A ∧ B] := by
  apply Exists.intro (fun _ => true)
  rfl

/-
Lets introduce a truth table tactic
-/
syntax "truth_table" ident " with " "[" (ident),* "]" (location)? : tactic
macro_rules
| `(tactic| truth_table $assign with [$ident] ) =>
    `(tactic| cases $assign $(quote ident.getId.toString))
| `(tactic| truth_table $assign with [$ident, $idents,*] ) =>
    `(tactic| truth_table $assign with [$ident] <;> truth_table $assign with [$idents,*])


example : IsContradiction [prop| (A → B) ∧ A ∧ ¬B] := by
  intro assign
  simp only [eval, Atom.eval]
  truth_table assign with [A, B] <;> decide

example : IsValid [prop| ¬((A → B) ∧ A ∧ ¬B)] := by
  intro assign
  simp only [eval, Atom.eval]
  truth_table assign with [A, B] <;> decide

/--
Definition 1.9
-/
def Equisatisfiable (lhs rhs : Formula) : Prop := IsSatisfiable lhs ↔ IsSatisfiable rhs

/--
Definition 1.10
-/
inductive NNF : Formula → Prop where
| atom (a : Atom) : NNF (.atom a)
| negAtom (a : Atom) : NNF (.neg (.atom a))
| and (lhs rhs : Formula) (h1 : NNF lhs) (h2 : NNF rhs) : NNF [prop| [t| lhs] ∧ [t| rhs]]
| or (lhs rhs : Formula) (h1 : NNF lhs) (h2 : NNF rhs) : NNF [prop| [t| lhs] ∨ [t| rhs]]


/--
Example
-/
example: ¬NNF [prop| ¬(x_1 ∨ x_2)] := by
  intro h
  cases h

example : NNF [prop| ¬x_1 ∧ ¬x_2] := by
  apply NNF.and
  apply NNF.negAtom
  apply NNF.negAtom

def toNNF : Formula → Formula
| [prop| ¬([t| a] ∨ [t| b])] => [prop| [t| toNNF <| .neg a] ∧ [t| toNNF <| .neg b]]
| [prop| ¬([t| a] ∧ [t| b])] => [prop| [t| toNNF <| .neg a] ∨ [t| toNNF <| .neg b]]
| .or lhs rhs => .or (toNNF lhs) (toNNF rhs)
| .and lhs rhs => .and (toNNF lhs) (toNNF rhs)
| .neg (.neg f) => toNNF f
| .atom a => .atom a
| .neg (.atom a) => .neg (.atom a)

-- TODO: remove these once mathlib updated
theorem not_and : ∀ a b : Bool, (!(a && b)) = (!a || !b) := by decide
theorem not_or : ∀ a b : Bool, (!(a || b)) = (!a && !b) := by decide
theorem eq_of_neg_eq : ∀ a b : Bool, (!a) = (!b) → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all

theorem negtoNNF_toNNFneg : ∀ (f : Formula) (assign : Assignment), (!eval assign (toNNF f)) = eval assign (toNNF (.neg f)) := by
  intro f assign
  induction f with
  | and lhs rhs lih rih =>
    simp only [toNNF, eval, not_and, lih, rih]
  | or lhs rhs lih rih =>
    simp only [toNNF, eval, not_or, lih, rih]
  | neg f ih =>
    simp only [←ih, toNNF, Bool.not_not]
  | atom => simp only [toNNF, eval]

theorem NNF_toNNF : ∀ f : Formula, NNF (toNNF f) := by
  intro f
  match hf:f with
  | and lhs rhs =>
    simp only [toNNF]
    apply NNF.and _ _ (NNF_toNNF _) (NNF_toNNF _)
  | or lhs rhs =>
    simp only [toNNF]
    apply NNF.or _ _ (NNF_toNNF _) (NNF_toNNF _)
  | neg nf =>
    match hnf:nf with
    | and lhs rhs =>
      simp only[toNNF] at *
      apply NNF.or _ _ (NNF_toNNF _) (NNF_toNNF _)
    | or lhs rhs =>
      simp only[toNNF] at *
      apply NNF.and _ _ (NNF_toNNF _) (NNF_toNNF _)
    | neg nnf =>
      simp only [toNNF]
      exact NNF_toNNF nnf
    | atom _ =>
      simp only [toNNF]
      apply NNF.negAtom
  | atom a =>
    simp only [toNNF]
    apply NNF.atom

theorem toNNF_preserves : ∀ (f : Formula) (assign : Assignment), eval assign f = eval assign (toNNF f) := by
  intro f assign
  induction f with
  | and lhs rhs lih rih => simp only [eval, toNNF, lih, rih]
  | or lsh rhs lih rih => simp only [eval, toNNF, lih, rih]
  | neg f ih =>
    cases f with
    | and lhs rhs =>
      simp only [eval, toNNF] at *
      simp only [negtoNNF_toNNFneg, ih, not_and]
    | or =>
      simp only [eval, toNNF] at *
      simp only [negtoNNF_toNNFneg, ih, not_or]
    | neg f =>
      simp only[toNNF, eval, Bool.not_not]
      cases f with
      | and =>
        simp only [toNNF, eval, ←not_and, ←negtoNNF_toNNFneg] at *
        apply eq_of_neg_eq
        assumption
      | or =>
        simp only [toNNF, eval, ←not_or, ←negtoNNF_toNNFneg] at *
        apply eq_of_neg_eq
        assumption
      | neg =>
        simp only[toNNF, eval, ←negtoNNF_toNNFneg, Bool.not_not] at *
        rw [ih]
      | atom => simp only[toNNF, eval]
    | atom => simp only[toNNF, eval]
  | atom =>
    simp only [toNNF, eval]

end Formula

end Decision.Propositional
