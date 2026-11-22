import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# L1: the drain machine, for an empty output alphabet

The decoder machine (`Monteverde.Function.Decoder`) needs an output alphabet with at least one
symbol. When the output alphabet `Δ` is empty, the only word over `Δ` is `[]`, so every function
into words over `Δ` has the output `[]`. The drain machine computes such a function: it pops the
input stack until it is empty, then halts with an empty output stack.

## Main results

* `Monteverde.Drain.drainer`: for an empty `Δ`, a `TM2ComputableInPolyTime` certificate for any
  function `f` from any encoding `e : α → List Γ` to any encoding `eo : β → List Δ`.
-/

namespace Monteverde.Drain

open Turing

variable (Γ Δ : Type)

/-- Stack alphabets: the input stack `false` holds `Γ`, the output stack `true` holds `Δ`. -/
@[reducible] def Gam : Bool → Type
  | false => Γ
  | true => Δ

/-- The program: one label. Pop the input; go on if a symbol came off, else halt. The state
records whether the last pop found a symbol. -/
def prog : Unit → TM2.Stmt (Gam Γ Δ) Unit Bool :=
  fun _ => .pop false (fun _ o => o.isSome) (.branch id (.goto fun _ => ()) .halt)

/-- The drain machine. -/
def tm [Fintype Γ] : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Gam Γ Δ
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Γ)
  m := prog Γ Δ

/-- The stacks of a configuration: the input, and an empty output. -/
def stk (inp : List Γ) : ∀ k, List (Gam Γ Δ k)
  | false => inp
  | true => []

variable {Γ Δ}

theorem update_input (inp inp' : List Γ) :
    Function.update (stk Γ Δ inp) false inp' = stk Γ Δ inp' := by
  funext k
  cases k <;> rfl

/-- The whole run: `|inp| + 1` steps empty the input stack and halt. -/
theorem run_all (inp : List Γ) (v : Bool) :
    (flip Option.bind (TM2.step (prog Γ Δ)))^[inp.length + 1]
        (some ⟨some (), v, stk Γ Δ inp⟩) = some ⟨none, false, stk Γ Δ []⟩ := by
  induction inp generalizing v with
  | nil =>
    change some (TM2.stepAux (.branch id (.goto fun _ => ()) .halt) false
      (Function.update (stk Γ Δ []) false [])) = _
    rw [update_input]
    rfl
  | cons a inp ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Option.bind (TM2.step (prog Γ Δ)))^[inp.length + 1]
      (some (TM2.stepAux (.branch id (.goto fun _ => ()) .halt) true
        (Function.update (stk Γ Δ (a :: inp)) false inp))) = _
    rw [update_input]
    exact ih true

theorem initList_eq [Fintype Γ] (inp : List Γ) :
    initList (tm Γ Δ) inp = ⟨some (), false, stk Γ Δ inp⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_eq [Fintype Γ] :
    haltList (tm Γ Δ) ([] : List Δ) = ⟨none, false, stk Γ Δ []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

theorem eq_nil [IsEmpty Δ] (l : List Δ) : l = [] := by
  cases l with
  | nil => rfl
  | cons a _ => exact isEmptyElim a

/-- The time bound `n + 1`. -/
noncomputable def time : Polynomial ℕ := Polynomial.X + Polynomial.C 1

/-- **The drainer.** For an empty output alphabet, the drain machine computes any function. -/
noncomputable def drainer [Fintype Γ] [IsEmpty Δ] {α β : Type} (e : α → List Γ)
    (eo : β → List Δ) (f : α → β) : TM2ComputableInPolyTime e eo f where
  tm := tm Γ Δ
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Δ
  time := time
  outputsFun a := by
    refine ⟨⟨(e a).length + 1, ?_⟩, by simp [time]⟩
    rw [eq_nil (eo (f a))]
    change (flip Option.bind (TM2.step (prog Γ Δ)))^[(e a).length + 1]
      (some (initList (tm Γ Δ) ((e a).map id))) = some (haltList (tm Γ Δ) (([] : List Δ).map id))
    erw [List.map_id, List.map_id, initList_eq, haltList_eq]
    exact run_all (e a) false

end Monteverde.Drain
