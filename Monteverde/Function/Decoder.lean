import Monteverde.Encoding.BlockEnc
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# L1: the decoder machine

The recoder (`Monteverde.Function.Recoder`) writes a word over a finite alphabet in the block
code. The reverse bridge for functions with word outputs also needs the other direction: a
Mathlib TM2 machine that reads the block code `blockEnc Δ y` of a word `y` and writes `y`.

In the block code, the symbol with index `i` is `frame (encUnary i)`: the bits `true true`,
`i` times, then `false`. The machine has three stacks (`none`: input bits, `some false`: work,
`some true`: output) and four labels:

* `read` pops one input bit. On `true` it jumps to `skip`, on `false` to `emit`, and on an empty
  input to `move`.
* `skip` pops the second `true` of a pair and adds one to the counter in the state.
* `emit` pushes the symbol whose index is the counter onto the work stack, and sets the counter
  back to `0`.
* `move` pops the work stack onto the output stack, one symbol per step, and halts when the work
  stack is empty. This reverses the work stack, so the output is in the right order.

The counter is a `Fin (card Δ)`, so the machine needs at least one symbol (`[Nonempty Δ]`). On
the block code of a word the counter never passes `card Δ - 1`.

## Main results

* `Monteverde.Decoder.decoder`: a `TM2ComputableInPolyTime` certificate for the identity
  function, from the encoding `fun b => blockEnc Δ (e b)` to the encoding `e : β → List Δ`.
-/

namespace Monteverde.Decoder

open Turing Turing.MultiTapeTM

variable (Δ : Type) [Fintype Δ] [Nonempty Δ]

/-- Stack alphabets: the input stack `none` holds bits, the other stacks hold symbols. -/
@[reducible] def Gam : Option Bool → Type
  | none => Bool
  | some _ => Δ

/-- Labels: `read`, `skip`, `emit`, `move`. -/
inductive Lab
  | read | skip | emit | move
  deriving DecidableEq

instance : Fintype Lab :=
  ⟨{.read, .skip, .emit, .move}, fun c => by cases c <;> decide⟩

/-- The number of symbols, counted with the `Fintype` instance that `encFinite` uses. -/
noncomputable def numSym : ℕ := @Fintype.card Δ (Fintype.ofFinite Δ)

/-- Symbol indices, in the order that `encFinite` uses. -/
noncomputable def eqv : Δ ≃ Fin (numSym Δ) := @Fintype.equivFin Δ (Fintype.ofFinite Δ)

theorem card_pos : 0 < numSym Δ := @Fintype.card_pos Δ (Fintype.ofFinite Δ) _

omit [Nonempty Δ] in
theorem encFinite_eq (a : Δ) : encFinite Δ a = List.replicate (eqv Δ a).val true := rfl

/-- States: the counter, the last popped input bit, and the last popped work symbol. -/
abbrev St : Type := Fin (numSym Δ) × Option Bool × Option Δ

/-- The counter value `0`. -/
noncomputable def zero : Fin (numSym Δ) := ⟨0, card_pos Δ⟩

/-- Add one to the counter, and stop at the largest value. -/
noncomputable def inc (c : Fin (numSym Δ)) : Fin (numSym Δ) :=
  if h : c.val + 1 < numSym Δ then ⟨c.val + 1, h⟩ else c

/-- The symbol with index `c`. -/
noncomputable def sym (c : Fin (numSym Δ)) : Δ := (eqv Δ).symm c

/-- After `read`: the next label from the popped bit. -/
def readNext (v : St Δ) : Lab :=
  match v.2.1 with
  | some true => .skip
  | some false => .emit
  | none => .move

/-- The program. -/
noncomputable def prog : Lab → TM2.Stmt (Gam Δ) Lab (St Δ)
  | .read => .pop none (fun v o => (v.1, o, v.2.2)) (.goto (readNext Δ))
  | .skip => .pop none (fun v _ => (inc Δ v.1, v.2)) (.goto fun _ => .read)
  | .emit =>
    .push (some false) (fun v => sym Δ v.1)
      (.load (fun v => (zero Δ, v.2)) (.goto fun _ => .read))
  | .move =>
    .pop (some false) (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.push (some true) (fun v => v.2.2.getD (Classical.arbitrary Δ))
          (.goto fun _ => .move))
        .halt)

/-- The decoder machine. -/
noncomputable def tm : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := some true
  Γ := Gam Δ
  Λ := Lab
  main := .read
  σ := St Δ
  initialState := (zero Δ, none, none)
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog Δ

/-- The stacks of a configuration. -/
def stk (inp : List Bool) (wk out : List Δ) : ∀ k, List (Gam Δ k)
  | none => inp
  | some false => wk
  | some true => out

/-- A configuration. -/
def cfg (l : Option Lab) (v : St Δ) (inp : List Bool) (wk out : List Δ) :
    TM2.Cfg (Gam Δ) Lab (St Δ) :=
  ⟨l, v, stk Δ inp wk out⟩

variable {Δ}

omit [Fintype Δ] [Nonempty Δ] in
theorem update_input (inp inp' : List Bool) (wk out : List Δ) :
    Function.update (stk Δ inp wk out) none inp' = stk Δ inp' wk out := by
  funext k
  rcases k with _ | _ | _ <;> rfl

omit [Fintype Δ] [Nonempty Δ] in
theorem update_work (inp : List Bool) (wk wk' out : List Δ) :
    Function.update (stk Δ inp wk out) (some false) wk' = stk Δ inp wk' out := by
  funext k
  rcases k with _ | _ | _ <;> rfl

omit [Fintype Δ] [Nonempty Δ] in
theorem update_output (inp : List Bool) (wk out out' : List Δ) :
    Function.update (stk Δ inp wk out) (some true) out' = stk Δ inp wk out' := by
  funext k
  rcases k with _ | _ | _ <;> rfl

/-- The step function. -/
noncomputable abbrev step : TM2.Cfg (Gam Δ) Lab (St Δ) → Option (TM2.Cfg (Gam Δ) Lab (St Δ)) :=
  TM2.step (prog Δ)

theorem step_read_true (v : St Δ) (inp : List Bool) (wk out : List Δ) :
    step (cfg Δ (some .read) v (true :: inp) wk out) =
      some (cfg Δ (some .skip) (v.1, some true, v.2.2) inp wk out) := by
  change some (TM2.stepAux (.goto (readNext Δ)) (v.1, some true, v.2.2)
    (Function.update (stk Δ (true :: inp) wk out) none inp)) = _
  rw [update_input]
  rfl

theorem step_read_false (v : St Δ) (inp : List Bool) (wk out : List Δ) :
    step (cfg Δ (some .read) v (false :: inp) wk out) =
      some (cfg Δ (some .emit) (v.1, some false, v.2.2) inp wk out) := by
  change some (TM2.stepAux (.goto (readNext Δ)) (v.1, some false, v.2.2)
    (Function.update (stk Δ (false :: inp) wk out) none inp)) = _
  rw [update_input]
  rfl

theorem step_read_nil (v : St Δ) (wk out : List Δ) :
    step (cfg Δ (some .read) v [] wk out) =
      some (cfg Δ (some .move) (v.1, none, v.2.2) [] wk out) := by
  change some (TM2.stepAux (.goto (readNext Δ)) (v.1, none, v.2.2)
    (Function.update (stk Δ [] wk out) none [])) = _
  rw [update_input]
  rfl

theorem step_skip (v : St Δ) (b : Bool) (inp : List Bool) (wk out : List Δ) :
    step (cfg Δ (some .skip) v (b :: inp) wk out) =
      some (cfg Δ (some .read) (inc Δ v.1, v.2) inp wk out) := by
  change some (TM2.stepAux (.goto fun _ => Lab.read) (inc Δ v.1, v.2)
    (Function.update (stk Δ (b :: inp) wk out) none inp)) = _
  rw [update_input]
  rfl

theorem step_emit (v : St Δ) (inp : List Bool) (wk out : List Δ) :
    step (cfg Δ (some .emit) v inp wk out) =
      some (cfg Δ (some .read) (zero Δ, v.2) inp (sym Δ v.1 :: wk) out) := by
  change some (TM2.stepAux (.load (fun v => (zero Δ, v.2)) (.goto fun _ => Lab.read)) v
    (Function.update (stk Δ inp wk out) (some false) (sym Δ v.1 :: wk))) = _
  rw [update_work]
  rfl

theorem step_move_cons (v : St Δ) (inp : List Bool) (a : Δ) (wk out : List Δ) :
    step (cfg Δ (some .move) v inp (a :: wk) out) =
      some (cfg Δ (some .move) (v.1, v.2.1, some a) inp wk (a :: out)) := by
  change some (TM2.stepAux
    (.branch (fun v => v.2.2.isSome)
      (.push (some true) (fun v => v.2.2.getD (Classical.arbitrary Δ))
        (.goto fun _ => Lab.move)) .halt)
    (v.1, v.2.1, some a) (Function.update (stk Δ inp (a :: wk) out) (some false) wk)) = _
  rw [update_work]
  change some (TM2.stepAux (.goto fun _ => Lab.move) (v.1, v.2.1, some a)
    (Function.update (stk Δ inp wk out) (some true) (a :: out))) = _
  rw [update_output]
  rfl

theorem step_move_nil (v : St Δ) (inp : List Bool) (out : List Δ) :
    step (cfg Δ (some .move) v inp [] out) =
      some (cfg Δ none (v.1, v.2.1, none) inp [] out) := by
  change some (TM2.stepAux
    (.branch (fun v => v.2.2.isSome)
      (.push (some true) (fun v => v.2.2.getD (Classical.arbitrary Δ))
        (.goto fun _ => Lab.move)) .halt)
    (v.1, v.2.1, none) (Function.update (stk Δ inp [] out) (some false) [])) = _
  rw [update_work]
  rfl

/-- Runs of the machine. -/
noncomputable abbrev run (n : ℕ) (c : TM2.Cfg (Gam Δ) Lab (St Δ)) :
    Option (TM2.Cfg (Gam Δ) Lab (St Δ)) :=
  (flip Option.bind step)^[n] (some c)

theorem run_succ {n : ℕ} {c c' : TM2.Cfg (Gam Δ) Lab (St Δ)} (h : step c = some c') :
    run (n + 1) c = run n c' := by
  simp only [run, Function.iterate_succ_apply]
  congr 1

theorem iterate_none (m : ℕ) :
    (flip Option.bind (step (Δ := Δ)))^[m] (none : Option (TM2.Cfg (Gam Δ) Lab (St Δ))) =
      none := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih

theorem run_add (m n : ℕ) (c : TM2.Cfg (Gam Δ) Lab (St Δ)) :
    run (m + n) c = (run n c).bind (run m) := by
  simp only [run]
  rw [Function.iterate_add_apply]
  cases (flip Option.bind (step (Δ := Δ)))^[n] (some c) with
  | none => exact iterate_none m
  | some c' => rfl

/-- The pairs `true true` of one symbol: each pair adds one to the counter. -/
theorem run_pairs (j : ℕ) (c : Fin (numSym Δ)) (hc : c.val + j < numSym Δ)
    (x : Option Bool) (y : Option Δ) (inp : List Bool) (wk : List Δ) :
    ∃ x', run (2 * j) (cfg Δ (some .read) (c, x, y)
        ((List.replicate j true).flatMap (fun b => [true, b]) ++ inp) wk []) =
      some (cfg Δ (some .read) (⟨c.val + j, hc⟩, x', y) inp wk []) := by
  induction j generalizing c x with
  | zero => exact ⟨x, rfl⟩
  | succ j ih =>
    have h1 : c.val + 1 < numSym Δ := by omega
    have hinc : inc Δ c = ⟨c.val + 1, h1⟩ := by simp [inc, h1]
    obtain ⟨x', hx'⟩ := ih ⟨c.val + 1, h1⟩ (by simp only; omega) (some true)
    refine ⟨x', ?_⟩
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ, List.flatMap_cons,
      show [true, true] ++ (List.replicate j true).flatMap (fun b => [true, b]) ++ inp =
        true :: true :: ((List.replicate j true).flatMap (fun b => [true, b]) ++ inp) by simp,
      run_succ (step_read_true _ _ _ _), run_succ (step_skip _ _ _ _ _), hinc]
    simp only at hx' ⊢
    rw [hx']
    congr 3
    simp only [Fin.mk.injEq]
    omega

/-- One symbol: from its block, the machine pushes it onto the work stack. -/
theorem run_symbol (a : Δ) (y : Option Δ) (x : Option Bool) (inp : List Bool) (wk : List Δ) :
    ∃ x', run (2 * (eqv Δ a).val + 2) (cfg Δ (some .read) (zero Δ, x, y)
        (frame (encFinite Δ a) ++ inp) wk []) =
      some (cfg Δ (some .read) (zero Δ, x', y) inp (a :: wk) []) := by
  have hfin : encFinite Δ a = List.replicate (eqv Δ a).val true := encFinite_eq Δ a
  have hlt := (eqv Δ a).isLt
  obtain ⟨x', hx'⟩ := run_pairs (Δ := Δ) (eqv Δ a).val (zero Δ)
    (by simp only [zero]; omega) x y (false :: inp) wk
  refine ⟨some false, ?_⟩
  rw [hfin, frame, List.append_assoc, show [false] ++ inp = false :: inp from rfl,
    show 2 * (eqv Δ a).val + 2 = 1 + 1 + 2 * (eqv Δ a).val by ring,
    run_add, hx', Option.bind_some, run_succ (step_read_false _ _ _ _),
    run_succ (step_emit _ _ _ _)]
  have hsym : sym Δ ⟨(zero Δ).val + (eqv Δ a).val, by simp only [zero]; omega⟩ = a := by
    simp only [sym, zero, Nat.zero_add, Fin.eta, Equiv.symm_apply_apply]
  rw [hsym]
  rfl

/-- The number of steps of the read phase on the block code of `y`. -/
noncomputable def readSteps (y : List Δ) : ℕ := (y.map fun a => 2 * (eqv Δ a).val + 2).sum

/-- The read phase: the machine pushes the decoded symbols onto the work stack. -/
theorem run_read (y : List Δ) (x : Option Bool) (z : Option Δ) (wk : List Δ) :
    ∃ x', run (readSteps y) (cfg Δ (some .read) (zero Δ, x, z) (blockEnc Δ y) wk []) =
      some (cfg Δ (some .read) (zero Δ, x', z) [] (y.reverse ++ wk) []) := by
  induction y generalizing x wk with
  | nil => exact ⟨x, rfl⟩
  | cons a y ih =>
    obtain ⟨x₁, h₁⟩ := run_symbol a z x (blockEnc Δ y) wk
    obtain ⟨x₂, h₂⟩ := ih x₁ (a :: wk)
    refine ⟨x₂, ?_⟩
    rw [readSteps, List.map_cons, List.sum_cons, Nat.add_comm, run_add,
      show blockEnc Δ (a :: y) = frame (encFinite Δ a) ++ blockEnc Δ y from rfl, h₁,
      Option.bind_some]
    rw [show (List.map (fun a => 2 * (eqv Δ a).val + 2) y).sum = readSteps y
      from rfl, h₂]
    simp

/-- The move phase: the work stack goes onto the output stack, in reverse order. -/
theorem run_move (wk : List Δ) (v : St Δ) (out : List Δ) :
    ∃ z, run wk.length (cfg Δ (some .move) v [] wk out) =
      some (cfg Δ (some .move) (v.1, v.2.1, z) [] [] (wk.reverse ++ out)) := by
  induction wk generalizing v out with
  | nil => exact ⟨v.2.2, rfl⟩
  | cons a wk ih =>
    obtain ⟨z, hz⟩ := ih (v.1, v.2.1, some a) (a :: out)
    refine ⟨z, ?_⟩
    rw [List.length_cons, run_succ (step_move_cons v [] a wk out), hz]
    simp

/-- The number of steps on the block code of `y`. -/
noncomputable def steps (y : List Δ) : ℕ := 1 + y.length + 1 + readSteps y

/-- The whole run, from the block code of `y` to `y`. -/
theorem run_all (y : List Δ) :
    run (steps y) (cfg Δ (some .read) (zero Δ, none, none) (blockEnc Δ y) [] []) =
      some (cfg Δ none (zero Δ, none, none) [] [] y) := by
  obtain ⟨x, hx⟩ := run_read y none none []
  obtain ⟨z, hz⟩ := run_move (y.reverse ++ []) (zero Δ, none, none) []
  rw [steps, run_add, hx, Option.bind_some, run_succ (step_read_nil _ _ _),
    show 1 + y.length = 1 + (y.reverse ++ []).length by simp, run_add, hz, Option.bind_some,
    show (1 : ℕ) = 0 + 1 from rfl, run_succ (step_move_nil _ _ _)]
  simp
  rfl

/-- The machine's start configuration is `cfg … w [] []`. -/
theorem initList_eq (w : List Bool) :
    initList (tm Δ) w = cfg Δ (some .read) (zero Δ, none, none) w [] [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with _ | _ | _ <;> rfl

/-- The machine's halt configuration with output `o` is `cfg none … [] [] o`. -/
theorem haltList_eq (o : List Δ) :
    haltList (tm Δ) o = cfg Δ none (zero Δ, none, none) [] [] o := by
  simp only [haltList, cfg]
  congr 1
  funext k
  rcases k with _ | _ | _ <;> rfl

omit [Nonempty Δ] in
theorem length_le_readSteps (y : List Δ) : readSteps y ≤ 2 * (blockEnc Δ y).length + 2 * y.length := by
  induction y with
  | nil => simp [readSteps]
  | cons a y ih =>
    have hfin : (encFinite Δ a).length = (eqv Δ a).val := by
      rw [encFinite_eq Δ a, List.length_replicate]
    have hframe : (frame (encFinite Δ a)).length = 2 * (encFinite Δ a).length + 1 := by
      simp [frame]
      ring
    simp only [readSteps, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [show blockEnc Δ (a :: y) = frame (encFinite Δ a) ++ blockEnc Δ y from rfl,
      List.length_append, hframe, hfin]
    omega

omit [Nonempty Δ] in
theorem length_le_blockEnc' (y : List Δ) : y.length ≤ (blockEnc Δ y).length := by
  induction y with
  | nil => simp
  | cons a y ih =>
    rw [show blockEnc Δ (a :: y) = frame (encFinite Δ a) ++ blockEnc Δ y from rfl,
      List.length_append, List.length_cons]
    have : 1 ≤ (frame (encFinite Δ a)).length := by simp [frame]
    omega

/-- The polynomial time bound `7 n + 2`. -/
noncomputable def time : Polynomial ℕ := Polynomial.C 7 * Polynomial.X + Polynomial.C 2

omit [Nonempty Δ] in
theorem steps_le (y : List Δ) : steps y ≤ time.eval (blockEnc Δ y).length := by
  have h1 := length_le_readSteps y
  have h2 := length_le_blockEnc' y
  simp only [steps, time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

/-- **The decoder.** For any encoding `e : β → List Δ`, the machine computes the identity from
the block code of `e` to `e` in polynomial time. -/
noncomputable def decoder {β : Type} (e : β → List Δ) :
    TM2ComputableInPolyTime (fun b => blockEnc Δ (e b)) e id where
  tm := tm Δ
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Δ
  time := time
  outputsFun b := by
    refine ⟨⟨steps (e b), ?_⟩, steps_le (e b)⟩
    change run (steps (e b)) (initList (tm Δ) ((blockEnc Δ (e b)).map id)) =
      some (haltList (tm Δ) ((e b).map id))
    erw [List.map_id, List.map_id, initList_eq, haltList_eq]
    exact run_all (e b)

end Monteverde.Decoder
