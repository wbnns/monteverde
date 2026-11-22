import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite work alphabets for Mathlib TM2 machines

Mathlib's `Turing.FinTM2` asks only the input alphabet `Γ k₀` to be finite. The stack alphabets
of the other stacks can be any types. The cslib-frontier bridge from TM2 machines
(`Turing.TM2ComputableInPolyTime.computableInPolyTime_encList`) needs every stack alphabet to be
finite.

This file closes that gap. A statement pushes only values `f s` with `f : σ → Γ k` and `s` in the
finite state type `σ`, so a machine pushes only finitely many symbols. We restrict each stack
alphabet to the symbols that can ever be on that stack: all of `Γ k₀`, all of `Γ k₁`, and the
pushed symbols. The restricted machine runs step by step like the original one.

## Main results

* `Monteverde.Finitize.finTM2`: the restricted machine.
* `Monteverde.Finitize.iterate_proj`: the restricted machine simulates the original one.
* `Monteverde.Finitize.exists_finite`: a polynomial-time TM2 certificate with a finite output
  alphabet gives one with all stack alphabets finite, for the same function and time bound.
-/

namespace Monteverde.Finitize

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

section Stmt

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- `Pushes q k x`: the statement `q` contains a push of the symbol `x` onto stack `k`. -/
inductive Pushes : TM2.Stmt Γ Λ σ → (k : K) → Γ k → Prop
  | here (k : K) (f : σ → Γ k) (q : TM2.Stmt Γ Λ σ) (s : σ) : Pushes (.push k f q) k (f s)
  | push {k' : K} {f : σ → Γ k'} {q : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q k x → Pushes (.push k' f q) k x
  | peek {k' : K} {f : σ → Option (Γ k') → σ} {q : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q k x → Pushes (.peek k' f q) k x
  | pop {k' : K} {f : σ → Option (Γ k') → σ} {q : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q k x → Pushes (.pop k' f q) k x
  | load {a : σ → σ} {q : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q k x → Pushes (.load a q) k x
  | branchL {f : σ → Bool} {q₁ q₂ : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q₁ k x → Pushes (.branch f q₁ q₂) k x
  | branchR {f : σ → Bool} {q₁ q₂ : TM2.Stmt Γ Λ σ} {k : K} {x : Γ k} :
      Pushes q₂ k x → Pushes (.branch f q₁ q₂) k x

/-- A statement pushes only finitely many symbols onto each stack. -/
theorem pushes_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) (k : K) : {x | Pushes q k x}.Finite := by
  induction q with
  | push k' f q ih =>
    by_cases hk : k' = k
    · subst hk
      refine ((Set.finite_range f).union ih).subset ?_
      intro x hx
      cases hx with
      | here _ _ _ s => exact Or.inl ⟨s, rfl⟩
      | push hq => exact Or.inr hq
    · refine ih.subset ?_
      intro x hx
      cases hx with
      | here => exact absurd rfl hk
      | push hq => exact hq
  | peek k' f q ih => exact ih.subset fun x hx => by cases hx with | peek hq => exact hq
  | pop k' f q ih => exact ih.subset fun x hx => by cases hx with | pop hq => exact hq
  | load a q ih => exact ih.subset fun x hx => by cases hx with | load hq => exact hq
  | branch f q₁ q₂ ih₁ ih₂ =>
    refine (ih₁.union ih₂).subset fun x hx => ?_
    cases hx with
    | branchL hq => exact Or.inl hq
    | branchR hq => exact Or.inr hq
  | goto f => exact Set.finite_empty.subset fun x hx => by cases hx
  | halt => exact Set.finite_empty.subset fun x hx => by cases hx

end Stmt

variable (tm : FinTM2)

/-- The symbols that can be on stack `k`: the input and output alphabets in full, and every
pushed symbol. -/
def Good (k : tm.K) (x : tm.Γ k) : Prop :=
  k = tm.k₀ ∨ k = tm.k₁ ∨ ∃ l, Pushes (tm.m l) k x

/-- The restricted stack alphabets. -/
abbrev Γ' (k : tm.K) : Type := {x : tm.Γ k // Good tm k x}

/-- Every input symbol is good. -/
theorem good_k₀ (x : tm.Γ tm.k₀) : Good tm tm.k₀ x := Or.inl rfl

/-- Every output symbol is good. -/
theorem good_k₁ (x : tm.Γ tm.k₁) : Good tm tm.k₁ x := Or.inr (Or.inl rfl)

/-- With a finite output alphabet, each restricted alphabet is finite. -/
theorem finite_Γ' [Finite (tm.Γ tm.k₁)] (k : tm.K) : Finite (Γ' tm k) := by
  have : {x | Good tm k x}.Finite := by
    have hpush : {x | ∃ l, Pushes (tm.m l) k x}.Finite := by
      have := Set.finite_iUnion (fun l => pushes_finite (tm.m l) k)
      simpa only [Set.ofPred_exists] using this
    by_cases h₀ : k = tm.k₀
    · subst h₀; exact Set.toFinite _
    by_cases h₁ : k = tm.k₁
    · subst h₁; exact Set.toFinite _
    refine hpush.subset fun x hx => ?_
    rcases hx with h | h | h
    · exact absurd h h₀
    · exact absurd h h₁
    · exact h
  exact this.to_subtype

/-- The restricted statement. The proof argument says that every symbol `q` pushes is good. -/
def restrict : (q : TM2.Stmt tm.Γ tm.Λ tm.σ) → (∀ k x, Pushes q k x → Good tm k x) →
    TM2.Stmt (Γ' tm) tm.Λ tm.σ
  | .push k f q, h =>
    .push k (fun s => ⟨f s, h k (f s) (.here k f q s)⟩)
      (restrict q fun k x hx => h k x (.push hx))
  | .peek k f q, h =>
    .peek k (fun s o => f s (o.map Subtype.val)) (restrict q fun k x hx => h k x (.peek hx))
  | .pop k f q, h =>
    .pop k (fun s o => f s (o.map Subtype.val)) (restrict q fun k x hx => h k x (.pop hx))
  | .load a q, h => .load a (restrict q fun k x hx => h k x (.load hx))
  | .branch f q₁ q₂, h =>
    .branch f (restrict q₁ fun k x hx => h k x (.branchL hx))
      (restrict q₂ fun k x hx => h k x (.branchR hx))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- The restricted program. -/
def m' (l : tm.Λ) : TM2.Stmt (Γ' tm) tm.Λ tm.σ :=
  restrict tm (tm.m l) fun _ _ hx => Or.inr (Or.inr ⟨l, hx⟩)

/-- The restricted machine. -/
noncomputable def finTM2 : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := Γ' tm
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := by
    have : Finite (Γ' tm tm.k₀) := Finite.of_injective Subtype.val Subtype.val_injective
    exact Fintype.ofFinite _
  m := m' tm

/-- Forget the restriction of a configuration. -/
def proj (c : TM2.Cfg (Γ' tm) tm.Λ tm.σ) : TM2.Cfg tm.Γ tm.Λ tm.σ :=
  ⟨c.l, c.var, fun k => (c.stk k).map Subtype.val⟩

theorem proj_injective : Function.Injective (proj tm) := by
  rintro ⟨l₁, v₁, S₁⟩ ⟨l₂, v₂, S₂⟩ h
  simp only [proj, TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl, rfl, hS⟩ := h
  have : S₁ = S₂ := funext fun k =>
    (List.map_injective_iff.mpr Subtype.val_injective) (congrFun hS k)
  subst this
  rfl

/-- One restricted statement runs like the original statement. -/
theorem stepAux_restrict (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (h : ∀ k x, Pushes q k x → Good tm k x)
    (v : tm.σ) (S : ∀ k, List (Γ' tm k)) :
    proj tm (TM2.stepAux (restrict tm q h) v S) =
      TM2.stepAux q v (fun k => (S k).map Subtype.val) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [restrict, TM2.stepAux]
    rw [ih]
    congr 1
    funext k'
    rw [Function.apply_update (fun k (l : List (Γ' tm k)) => l.map Subtype.val)]
    rfl
  | peek k f q ih =>
    simp only [restrict, TM2.stepAux]
    rw [ih, List.head?_map]
  | pop k f q ih =>
    simp only [restrict, TM2.stepAux]
    rw [ih, List.head?_map]
    congr 1
    funext k'
    rw [Function.apply_update (fun k (l : List (Γ' tm k)) => l.map Subtype.val)]
    simp only [List.map_tail]
  | load a q ih =>
    simp only [restrict, TM2.stepAux]
    rw [ih]
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [restrict, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

/-- One step of the restricted machine projects to one step of the original machine. -/
theorem step_proj (c : TM2.Cfg (Γ' tm) tm.Λ tm.σ) :
    Option.map (proj tm) (TM2.step (m' tm) c) = TM2.step tm.m (proj tm c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
    change some (proj tm (TM2.stepAux (m' tm l) v S)) =
      some (TM2.stepAux (tm.m l) v (fun k => (S k).map Subtype.val))
    exact congrArg some (stepAux_restrict tm _ _ v S)

/-- Runs of the restricted machine project to runs of the original machine. -/
theorem iterate_proj (n : ℕ) (o : Option (TM2.Cfg (Γ' tm) tm.Λ tm.σ)) :
    Option.map (proj tm) ((flip Option.bind (TM2.step (m' tm)))^[n] o) =
      (flip Option.bind (TM2.step tm.m))^[n] (Option.map (proj tm) o) := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    cases o with
    | none => rfl
    | some c => exact step_proj tm c

/-- The restricted input alphabet is the full input alphabet. -/
def inputEquiv : (finTM2 tm).Γ (finTM2 tm).k₀ ≃ tm.Γ tm.k₀ :=
  Equiv.subtypeUnivEquiv (good_k₀ tm)

/-- The restricted output alphabet is the full output alphabet. -/
def outputEquiv : (finTM2 tm).Γ (finTM2 tm).k₁ ≃ tm.Γ tm.k₁ :=
  Equiv.subtypeUnivEquiv (good_k₁ tm)

theorem map_val_symm {X : Type} {p : X → Prop} (h : ∀ x, p x) (s : List X) :
    (s.map (Equiv.subtypeUnivEquiv h).symm).map Subtype.val = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.map_cons, ih]; rfl

theorem initList_stk_k₀ (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : (initList tm s).stk tm.k₀ = s := by
  simp [initList]

theorem initList_stk_ne (tm : FinTM2) (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := by
  simp [initList, h]

theorem haltList_stk_k₁ (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

theorem haltList_stk_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := by
  simp [haltList, h]

theorem proj_initList (s : List (tm.Γ tm.k₀)) :
    proj tm (initList (finTM2 tm) (s.map (inputEquiv tm).symm)) = initList tm s := by
  unfold proj
  rw [show initList tm s = ⟨some tm.main, tm.initialState, (initList tm s).stk⟩ from rfl]
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h
    rw [initList_stk_k₀ tm s]
    exact (congrArg _ (initList_stk_k₀ (finTM2 tm) _)).trans
      (map_val_symm _ s)
  · rw [initList_stk_ne tm s h]
    exact (congrArg _ (initList_stk_ne (finTM2 tm) _ h)).trans rfl

theorem proj_haltList (s : List (tm.Γ tm.k₁)) :
    proj tm (haltList (finTM2 tm) (s.map (outputEquiv tm).symm)) = haltList tm s := by
  unfold proj
  rw [show haltList tm s = ⟨none, tm.initialState, (haltList tm s).stk⟩ from rfl]
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h
    rw [haltList_stk_k₁ tm s]
    exact (congrArg _ (haltList_stk_k₁ (finTM2 tm) _)).trans
      (map_val_symm _ s)
  · rw [haltList_stk_ne tm s h]
    exact (congrArg _ (haltList_stk_ne (finTM2 tm) _ h)).trans rfl

/-- The restricted machine gives the same outputs in the same time. -/
noncomputable def outputsInTime {s : List (tm.Γ tm.k₀)} {s' : List (tm.Γ tm.k₁)} {t : ℕ}
    (h : TM2OutputsInTime tm s (some s') t) :
    TM2OutputsInTime (finTM2 tm) (s.map (inputEquiv tm).symm)
      (some (s'.map (outputEquiv tm).symm)) t where
  steps := h.steps
  evals_in_steps := by
    have hn : (flip Option.bind (TM2.step tm.m))^[h.steps] (some (initList tm s)) =
        some (haltList tm s') := h.evals_in_steps
    generalize h.steps = n at hn ⊢
    have key : Option.map (proj tm) ((flip Option.bind (TM2.step (m' tm)))^[n]
        (some (initList (finTM2 tm) (s.map (inputEquiv tm).symm)))) =
        Option.map (proj tm) (some (haltList (finTM2 tm) (s'.map (outputEquiv tm).symm))) := by
      rw [iterate_proj]
      change (flip Option.bind (TM2.step tm.m))^[n]
          (some (proj tm (initList (finTM2 tm) (s.map (inputEquiv tm).symm)))) =
        some (proj tm (haltList (finTM2 tm) (s'.map (outputEquiv tm).symm)))
      rw [proj_initList, proj_haltList]
      exact hn
    exact Option.map_injective (proj_injective tm) key
  steps_le_m := h.steps_le_m

end Monteverde.Finitize

namespace Monteverde

open Turing

/-- **Finite work alphabets.** A polynomial-time TM2 certificate with a finite output alphabet
gives one, for the same function and time bound, whose stack alphabets are all finite. -/
theorem TM2ComputableInPolyTime.exists_finite {α β αΓ βΓ : Type} [Finite βΓ]
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    ∃ h' : TM2ComputableInPolyTime ea eb f, ∀ k, Finite (h'.tm.Γ k) := by
  have : Finite (h.tm.Γ h.tm.k₁) := Finite.of_equiv _ h.outputAlphabet.symm
  refine ⟨{ tm := Finitize.finTM2 h.tm
            inputAlphabet := (Finitize.inputEquiv h.tm).trans h.inputAlphabet
            outputAlphabet := (Finitize.outputEquiv h.tm).trans h.outputAlphabet
            time := h.time
            outputsFun := fun a => ?_ }, fun k => Finitize.finite_Γ' h.tm k⟩
  have := Finitize.outputsInTime h.tm (h.outputsFun a)
  simpa [List.map_map, Function.comp_def] using this

end Monteverde
