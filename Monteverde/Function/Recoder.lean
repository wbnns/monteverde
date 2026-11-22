import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# L1: the recoder machine

The reverse bridge (cslib-frontier to Clay) needs one new machine: a Mathlib TM2 machine that
reads a word `w` over a finite alphabet `Γ` and writes the binary word `w.flatMap code`, for a
fixed symbol code `code : Γ → List Bool`. With `code a = frame (encFinite Γ a)` this is the block
code `blockEnc Γ w`.

The machine has three stacks (`none`: input over `Γ`, `some false`: work, `some true`: output)
and three kinds of labels:

* `read` pops one input symbol `a` and jumps to `emit a`, or to `move` when the input is empty;
* `emit a` pushes the bits of `code a` onto the work stack in one statement, then jumps back to
  `read`;
* `move` pops the work stack onto the output stack, one bit per step, and halts when the work
  stack is empty. This reverses the work stack, so the output is in the right order.

One TM2 step runs a whole statement, so the machine runs in `2 n + m + 2` steps, where `n` is the
input length and `m` the output length.

## Main results

* `Monteverde.Recoder.recoder`: a `TM2ComputableInPolyTime` certificate for the identity function,
  from an encoding `e : α → List Γ` to the encoding `fun a => (e a).flatMap code`.
-/

namespace Monteverde.Recoder

open Turing

variable (Γ : Type) (code : Γ → List Bool)

/-- Stack alphabets: the input stack `none` holds symbols, the other stacks hold bits. -/
@[reducible] def Gam : Option Bool → Type
  | none => Γ
  | some _ => Bool

/-- Labels: `inl a` is `emit a`, `inr false` is `read`, `inr true` is `move`. -/
abbrev Lab : Type := Γ ⊕ Bool

/-- States: the last popped input symbol and the last popped work bit. -/
abbrev St : Type := Option Γ × Option Bool

/-- Push a fixed list of bits onto the work stack, in order. -/
def pushBits : List Bool → TM2.Stmt (Gam Γ) (Lab Γ) (St Γ) → TM2.Stmt (Gam Γ) (Lab Γ) (St Γ)
  | [], q => q
  | b :: bs, q => .push (some false) (fun _ => b) (pushBits bs q)

/-- After `read`: emit the popped symbol, or move when the input is empty. -/
def readNext (v : St Γ) : Lab Γ :=
  match v.1 with
  | some a => .inl a
  | none => .inr true

/-- The program. -/
def prog : Lab Γ → TM2.Stmt (Gam Γ) (Lab Γ) (St Γ)
  | .inr false => .pop none (fun v o => (o, v.2)) (.goto (readNext Γ))
  | .inl a => pushBits Γ (code a) (.goto fun _ => .inr false)
  | .inr true =>
    .pop (some false) (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.push (some true) (fun v => v.2.getD false) (.goto fun _ => .inr true))
        .halt)

/-- The recoder machine. -/
noncomputable def tm [Fintype Γ] : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := some true
  Γ := Gam Γ
  Λ := Lab Γ
  main := .inr false
  σ := St Γ
  initialState := (none, none)
  Γk₀Fin := (inferInstance : Fintype Γ)
  m := prog Γ code

/-- The stacks of a configuration. -/
def stk (inp : List Γ) (wk out : List Bool) : ∀ k, List (Gam Γ k)
  | none => inp
  | some false => wk
  | some true => out

/-- A configuration. -/
def cfg (l : Option (Lab Γ)) (v : St Γ) (inp : List Γ) (wk out : List Bool) :
    TM2.Cfg (Gam Γ) (Lab Γ) (St Γ) :=
  ⟨l, v, stk Γ inp wk out⟩

variable {Γ}

theorem update_input (inp inp' : List Γ) (wk out : List Bool) :
    Function.update (stk Γ inp wk out) none inp' = stk Γ inp' wk out := by
  funext k
  rcases k with _ | _ | _ <;> rfl

theorem update_work (inp : List Γ) (wk wk' out : List Bool) :
    Function.update (stk Γ inp wk out) (some false) wk' = stk Γ inp wk' out := by
  funext k
  rcases k with _ | _ | _ <;> rfl

theorem update_output (inp : List Γ) (wk out out' : List Bool) :
    Function.update (stk Γ inp wk out) (some true) out' = stk Γ inp wk out' := by
  funext k
  rcases k with _ | _ | _ <;> rfl

theorem stepAux_pushBits (bs : List Bool) (q : TM2.Stmt (Gam Γ) (Lab Γ) (St Γ)) (v : St Γ)
    (inp : List Γ) (wk out : List Bool) :
    TM2.stepAux (pushBits Γ bs q) v (stk Γ inp wk out) =
      TM2.stepAux q v (stk Γ inp (bs.reverse ++ wk) out) := by
  induction bs generalizing wk with
  | nil => rfl
  | cons b bs ih =>
    simp only [pushBits, TM2.stepAux]
    change TM2.stepAux (pushBits Γ bs q) v
      (Function.update (stk Γ inp wk out) (some false) (b :: wk)) = _
    rw [update_work, ih]
    simp

/-- The step function. -/
abbrev step : TM2.Cfg (Gam Γ) (Lab Γ) (St Γ) → Option (TM2.Cfg (Gam Γ) (Lab Γ) (St Γ)) :=
  TM2.step (prog Γ code)

theorem step_read_cons (v : St Γ) (a : Γ) (inp : List Γ) (wk out : List Bool) :
    step code (cfg Γ (some (.inr false)) v (a :: inp) wk out) =
      some (cfg Γ (some (.inl a)) (some a, v.2) inp wk out) := by
  change some (TM2.stepAux (.goto (readNext Γ)) (some a, v.2)
    (Function.update (stk Γ (a :: inp) wk out) none inp)) = _
  rw [update_input]
  rfl

theorem step_read_nil (v : St Γ) (wk out : List Bool) :
    step code (cfg Γ (some (.inr false)) v [] wk out) =
      some (cfg Γ (some (.inr true)) (none, v.2) [] wk out) := by
  change some (TM2.stepAux (.goto (readNext Γ)) (none, v.2)
    (Function.update (stk Γ [] wk out) none [])) = _
  rw [update_input]
  rfl

theorem step_emit (v : St Γ) (a : Γ) (inp : List Γ) (wk out : List Bool) :
    step code (cfg Γ (some (.inl a)) v inp wk out) =
      some (cfg Γ (some (.inr false)) v inp ((code a).reverse ++ wk) out) := by
  change some (TM2.stepAux (pushBits Γ (code a) (.goto fun _ => .inr false)) v
    (stk Γ inp wk out)) = _
  rw [stepAux_pushBits]
  rfl

theorem step_move_cons (v : St Γ) (inp : List Γ) (b : Bool) (wk out : List Bool) :
    step code (cfg Γ (some (.inr true)) v inp (b :: wk) out) =
      some (cfg Γ (some (.inr true)) (v.1, some b) inp wk (b :: out)) := by
  change some (TM2.stepAux
    (.branch (fun v => v.2.isSome)
      (.push (some true) (fun v => v.2.getD false) (.goto fun _ => (Sum.inr true : Lab Γ))) .halt)
    (v.1, some b) (Function.update (stk Γ inp (b :: wk) out) (some false) wk)) = _
  rw [update_work]
  change some (TM2.stepAux (.goto fun _ => (Sum.inr true : Lab Γ)) (v.1, some b)
    (Function.update (stk Γ inp wk out) (some true) (b :: out))) = _
  rw [update_output]
  rfl

theorem step_move_nil (v : St Γ) (inp : List Γ) (out : List Bool) :
    step code (cfg Γ (some (.inr true)) v inp [] out) =
      some (cfg Γ none (v.1, none) inp [] out) := by
  change some (TM2.stepAux
    (.branch (fun v => v.2.isSome)
      (.push (some true) (fun v => v.2.getD false) (.goto fun _ => (Sum.inr true : Lab Γ))) .halt)
    (v.1, none) (Function.update (stk Γ inp [] out) (some false) [])) = _
  rw [update_work]
  rfl

/-- Runs of the machine. -/
abbrev run (n : ℕ) (c : TM2.Cfg (Gam Γ) (Lab Γ) (St Γ)) :
    Option (TM2.Cfg (Gam Γ) (Lab Γ) (St Γ)) :=
  (flip Option.bind (step code))^[n] (some c)

theorem run_succ {n : ℕ} {c c' : TM2.Cfg (Gam Γ) (Lab Γ) (St Γ)} (h : step code c = some c') :
    run code (n + 1) c = run code n c' := by
  simp only [run, Function.iterate_succ_apply]
  congr 1

theorem iterate_none (m : ℕ) :
    (flip Option.bind (step code))^[m] (none : Option (TM2.Cfg (Gam Γ) (Lab Γ) (St Γ))) = none := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih

theorem run_add (m n : ℕ) (c : TM2.Cfg (Gam Γ) (Lab Γ) (St Γ)) :
    run code (m + n) c = (run code n c).bind (run code m) := by
  simp only [run]
  rw [Function.iterate_add_apply]
  cases (flip Option.bind (step code))^[n] (some c) with
  | none => exact iterate_none code m
  | some c' => rfl

/-- The read phase: `read` and `emit` copy the codes of all input symbols to the work stack. -/
theorem run_read (inp : List Γ) (v : St Γ) (wk : List Bool) :
    ∃ x, run code (2 * inp.length) (cfg Γ (some (.inr false)) v inp wk []) =
      some (cfg Γ (some (.inr false)) (x, v.2) [] ((inp.flatMap code).reverse ++ wk) []) := by
  induction inp generalizing v wk with
  | nil => exact ⟨v.1, rfl⟩
  | cons a inp ih =>
    obtain ⟨x, hx⟩ := ih (some a, v.2) ((code a).reverse ++ wk)
    refine ⟨x, ?_⟩
    rw [show 2 * (a :: inp).length = 2 * inp.length + 1 + 1 by simp; ring,
      run_succ code (step_read_cons code v a inp wk []),
      run_succ code (step_emit code (some a, v.2) a inp wk []), hx]
    simp [List.flatMap_cons, List.reverse_append, List.append_assoc]

/-- The move phase: the work stack goes onto the output stack, in reverse order. -/
theorem run_move (wk : List Bool) (v : St Γ) (out : List Bool) :
    ∃ y, run code wk.length (cfg Γ (some (.inr true)) v [] wk out) =
      some (cfg Γ (some (.inr true)) (v.1, y) [] [] (wk.reverse ++ out)) := by
  induction wk generalizing v out with
  | nil => exact ⟨v.2, rfl⟩
  | cons b wk ih =>
    obtain ⟨y, hy⟩ := ih (v.1, some b) (b :: out)
    refine ⟨y, ?_⟩
    rw [List.length_cons, run_succ code (step_move_cons code v [] b wk out), hy]
    simp

/-- The number of steps on an input word. -/
def steps (w : List Γ) : ℕ := 1 + (w.flatMap code).length + 1 + 2 * w.length

/-- The whole run, from the input word to the output word. -/
theorem run_all (w : List Γ) :
    run code (steps code w) (cfg Γ (some (.inr false)) (none, none) w [] []) =
      some (cfg Γ none (none, none) [] [] (w.flatMap code)) := by
  obtain ⟨x, hx⟩ := run_read code w (none, none) []
  obtain ⟨y, hy⟩ := run_move code ((w.flatMap code).reverse ++ []) (none, none) []
  rw [steps, run_add, hx, Option.bind_some, run_succ code (step_read_nil code _ _ _),
    show 1 + (w.flatMap code).length = 1 + ((w.flatMap code).reverse ++ []).length by simp,
    run_add, hy, Option.bind_some, show (1 : ℕ) = 0 + 1 from rfl,
    run_succ code (step_move_nil code _ _ _)]
  simp
  rfl

/-- The machine's start configuration is `cfg … w [] []`. -/
theorem initList_eq [Fintype Γ] (w : List Γ) :
    initList (tm Γ code) w = cfg Γ (some (.inr false)) (none, none) w [] [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with _ | _ | _ <;> rfl

/-- The machine's halt configuration with output `o` is `cfg none … [] [] o`. -/
theorem haltList_eq [Fintype Γ] (o : List Bool) :
    haltList (tm Γ code) o = cfg Γ none (none, none) [] [] o := by
  simp only [haltList, cfg]
  congr 1
  funext k
  rcases k with _ | _ | _ <;> rfl

/-- An upper bound on the length of any symbol code. -/
noncomputable def codeBound [Fintype Γ] : ℕ := ∑ a, (code a).length

theorem length_code_le [Fintype Γ] (a : Γ) : (code a).length ≤ codeBound code :=
  Finset.single_le_sum (f := fun a => (code a).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)

theorem length_flatMap_le [Fintype Γ] (w : List Γ) : (w.flatMap code).length ≤ codeBound code * w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := length_code_le code a
    nlinarith

/-- The polynomial time bound `(C + 2) n + 2`. -/
noncomputable def time [Fintype Γ] : Polynomial ℕ :=
  Polynomial.C (codeBound code + 2) * Polynomial.X + Polynomial.C 2

theorem steps_le [Fintype Γ] (w : List Γ) : steps code w ≤ (time code).eval w.length := by
  have := length_flatMap_le code w
  simp only [steps, time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  nlinarith

/-- **The recoder.** For any encoding `e : α → List Γ`, the machine computes the identity from
`e` to `fun a => (e a).flatMap code` in polynomial time. -/
noncomputable def recoder [Fintype Γ] {α : Type} (e : α → List Γ) :
    TM2ComputableInPolyTime e (fun a => (e a).flatMap code) id where
  tm := tm Γ code
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Bool
  time := time code
  outputsFun a := by
    refine ⟨⟨steps code (e a), ?_⟩, steps_le code (e a)⟩
    change run code (steps code (e a)) (initList (tm Γ code) ((e a).map id)) =
      some (haltList (tm Γ code) (((e a).flatMap code).map id))
    erw [List.map_id, List.map_id, initList_eq, haltList_eq]
    exact run_all code (e a)

end Monteverde.Recoder
