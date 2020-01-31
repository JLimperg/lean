/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category.monad init.category.alternative init.meta.format init.util
/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/
/-- An exceptional is similar to `Result` in Haskell.-/
meta inductive exceptional (α : Type)
| success   : α → exceptional
| exception : (options → format) → exceptional

section
open exceptional
variables {α : Type}
variables [has_to_string α]

protected meta def exceptional.to_string : exceptional α → string
| (success a)       := to_string a
| (exception .(α) e) := "Exception: " ++ to_string (e options.mk)

meta instance : has_to_string (exceptional α) :=
has_to_string.mk exceptional.to_string
end

namespace exceptional
variables {α β : Type}

protected meta def to_bool : exceptional α → bool
| (success _)      := tt
| (exception .(α) _) := ff

protected meta def to_option : exceptional α → option α
| (success a)      := some a
| (exception .(α) _) := none

@[inline] protected meta def bind (e₁ : exceptional α) (e₂ : α → exceptional β) : exceptional β :=
exceptional.cases_on e₁
  (λ a, e₂ a)
  (λ f, exception β f)

@[inline] protected meta def return (a : α) : exceptional α :=
success a

@[inline] meta def fail (f : format) : exceptional α :=
exception α (λ u, f)

protected meta def orelse {α} : exceptional α → exceptional α → exceptional α
| (success x) _ := success x
| (exception _ _) y := y
end exceptional

meta instance : monad exceptional :=
{pure := @exceptional.return, bind := @exceptional.bind}

/-
Note these caveats:

* `failure` does not provide an informative error message, so `fail` should
  usually be preferred.
* When you write `orelse x y`, both `x` and `y` will always be evaluated.
* This instance is not law-abiding: `orelse (exception _ x) failure` should be
  `exception _ x` but is `failure`.
-/
meta instance : alternative exceptional :=
{orelse := @exceptional.orelse,
failure := λ {_}, exceptional.fail format.nil}
