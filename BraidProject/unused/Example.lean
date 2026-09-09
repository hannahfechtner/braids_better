import Mathlib.Tactic

/- First look at Lean -/

-- An informal proof explains to a human reader why a statement
-- is true. A formal proof is written in a precise language that
-- a computer can check. Lean is an interactive theorem prover,
-- also called a proof assistant. Its kernel is the small trusted
-- core that checks terms and proofs. Mathlib supplies
-- definitions, notation, theorems, and additional tactics. In VS
-- Code, the Infoview reports types and displays the current
-- proof state.

-- The opening `import Mathlib.Tactic` makes Mathlib's library and
-- tactics available in this file.


section TermsAndTypes

-- A term is an expression such as a numeral, string, function,
-- or proof. A type classifies the terms that may be used where
-- that type is expected. The typing judgment `a : A` says that
-- the term `a` has type `A`.

-- Elaboration interprets notation and fills in information that
-- Lean can infer. `#check` elaborates an expression and reports
-- its type.

#check Nat

-- `ℕ`, entered with `\N` in VS Code, abbreviates `Nat`.

#check ℕ

-- `Nat : Type` says that `Nat` is a type.

#check 5

-- A type annotation asks Lean to interpret an expression at the
-- stated type. The numeral token is the same; the annotations
-- request different types.

#check (5 : Int)   -- Lean prints the integer type as `ℤ`
#check (5 : ℝ)

#check String
#check "hello"

end TermsAndTypes

-- Once Lean has assigned types to expressions, definitions give
-- names to terms, and `#eval` computes executable expressions.


section DefinitionsAndComputation

-- A line comment begins with `--`. A block comment begins with
-- `/-` and ends with `-/`.

-- `def` creates a reusable named declaration in Lean's global
-- environment.

def my_fav_number : Nat := 27

-- Here `n` is the name, `Nat` is the declared type, and `1` is
-- the body.

-- These commands ask three different questions.

#check my_fav_number       -- What is the type of this expression?
#print my_fav_number       -- What declaration is stored under this name?
#eval my_fav_number + 1    -- What value does this expression compute?

end DefinitionsAndComputation


-- The same elaboration process checks anonymous examples and
-- tactic proofs.


section DeclarationsAndProofStates

-- `example` checks a term of a stated type without giving it a
-- reusable name. Its header lists parameters and the required
-- type; `:=` separates the body. Writing the required term
-- directly after `:=` is term mode.

example (A : Type) (a : A) : A :=
  sorry

-- Parameters of the same type may be grouped: `(a b : A)`
-- abbreviates `(a : A) (b : A)`.

-- Parentheses mark explicit parameters; braces mark parameters
-- Lean tries to infer.

def foo {A : Type} (a : A) : A :=
  sorry

#check ()

variable {A : Type} (a : A)
#check foo a
-- `by` begins tactic mode, where tactics construct the term step
-- by step. A proof state has zero or more goals. Each goal has a
-- local context and a target. The context appears above `⊢`; the
-- target, the type still required, appears after it. A tactic
-- changes the proof state as Lean builds the term checked by the
-- kernel.

example (A : Type) (a : A) : A := by
  sorry

-- A named definition creates a global declaration available
-- later. Parameters create local declarations available only
-- within the current declaration. A local declaration may
-- introduce a type or term; it need not be an assumption.

-- Two tactics close the goal above from the local context.
-- `exact a` supplies the named term `a`. `assumption` searches
-- the local context for a term of the required type instead of
-- naming one.

def foo1 (a b : Nat) : Nat := by
  show_term
  assumption

#eval foo1 3 5

-- `sorry` is a placeholder accepted with a warning while work is
-- incomplete. It is not a proof technique; completed code
-- replaces it with a term or tactic proof.

end DeclarationsAndProofStates


-- When the required type is a proposition, constructing its term
-- is proving it.


section PropositionsAndProofs

-- Lean uses the same terms-and-types framework for logic.
-- `P : Prop` says that `P` is a proposition. `h : P` says that
-- `h` is a proof of `P`; `h` is a proof term. Lean's core logic
-- is constructive: proving `P` requires constructing such
-- evidence. Within a section, `variable` introduces names that
-- subsequent commands and examples may use without repeating
-- them.

variable (P : Prop) (h : P)

#check P
#check h

-- A proof may be supplied directly in term mode or constructed
-- in tactic mode.

example : P :=
  sorry

example : P := by
  sorry

-- Within a proof, `h : P` appears in the local context as a
-- hypothesis. `theorem` and `lemma` create reusable named proof
-- terms; their headers list their own parameters.

lemma proof_from_hypothesis {P : Prop} (h : P) : P :=
  h

#check proof_from_hypothesis h

-- Lean infers the lemma's implicit proposition argument from the
-- type of `h`.

theorem proof_from_hypothesis_again
    (P : Prop) (h : P) : P := by
  exact h

-- The name of a proved theorem is itself a proof term and may be
-- used later. Treating propositions as types and proofs as terms
-- is the propositions-as-types interpretation.

end PropositionsAndProofs


-- Curry–Howard explains the parallel between type constructions
-- and corresponding logical forms.


section CurryHoward

/-
The Curry–Howard correspondence matches logical forms and proof
rules with parallel type constructions and operations on terms,
without identifying them. In this comparison, `A` and `B` are
types, `P` and `Q` are propositions, `R : A → Prop` assigns a
proposition to each `x : A`, and `C : A → Type` assigns a type.

* a proposition `P : Prop` and a type `A : Type`;
* implication `P → Q` and a function type `A → B`;
* conjunction `P ∧ Q` and a product type `A × B`;
* disjunction `P ∨ Q` and a sum type `A ⊕ B`;
* `True` and `Unit`;
* `False` and `Empty`;
* universal quantification `∀ x : A, R x` and a dependent
  function type `(x : A) → C x`;
* existential quantification `∃ x : A, R x` and a dependent pair
  type `Σ x : A, C x`.

The last two rows are dependent: `R x` and `C x` vary with the
input `x`.

A proof is a term whose type is the proposition it proves. The
account of what counts as a proof of each form is the
Brouwer–Heyting–Kolmogorov (BHK) interpretation.
-/

end CurryHoward

#check Exists

def exists_even : ∃ (n : Nat), Even n := by
  use 2
  unfold Even
  use 1

def exists_even' : ∃ (n : Nat), Even n := by
  use 18
  unfold Even
  use 9

def proofs_are_the_same : exists_even = exists_even' := by rfl
