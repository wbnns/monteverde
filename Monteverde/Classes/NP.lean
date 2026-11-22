import Monteverde.Classes.P
import Monteverde.Encoding.Pair
import Monteverde.Encoding.Certificate
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# L2: Clay's NP and cslib-frontier's NP

For a finite alphabet `Γ`, a language over `Γ` is in Clay's `InNondeterministicPolynomialTime`
exactly when it is in cslib-frontier's `NP` under the block code `blockEnc Γ`.

The definitions differ in four ways, and the proof handles each one:

* certificates: Clay allows any finite alphabet `Γ₁`, cslib-frontier uses bits. We read Clay
  certificates with the decoder `certDecoder` (in `Monteverde.Encoding.Certificate`).
* length: Clay bounds certificates by `|w| ^ k`, cslib-frontier fixes the length to `p (n)`
  for the encoded length `n`. Padding (`mem_NP_of_check`) covers one direction. For the other
  direction, words of length 0 and 1 get the empty certificate, because `|w| ^ k ≤ 1` there.
* checking: Clay checks the pair word `w#y` with a TM2 machine, cslib-frontier checks `encPair`
  with a Boolean verifier. `pairWord`, `lefts` and `rights` (in `Monteverde.Encoding.Pair`) move
  between the forms, and the L1 bridge moves between the machine models.
* relations: Clay uses a `Prop` relation, cslib-frontier a `Bool` verifier.
-/

namespace Monteverde

open Turing Turing.MultiTapeTM Cslib.Complexity

section ClayToCslib

variable {Γ : Type} [Fintype Γ]

/-- The certificate check used for a Clay verifier: a certificate must be present, short enough,
and accepted by the Clay checker `f`. -/
def clayCheck {Δ : Type} (k : ℕ) (f : List Γ × List Δ → Bool)
    (x : List Γ × Option (List Δ)) : Bool :=
  x.2.elim false fun y => decide (y.length ≤ x.1.length ^ k) && f (x.1, y)

theorem clayCheck_polyTime {Δ : Type} [Fintype Δ] (k : ℕ) {f : List Γ × List Δ → Bool}
    (hf : ComputableInPolyTime f (encPair (blockEnc Γ) (blockEnc Δ)) encBool) :
    ComputableInPolyTime (clayCheck k f)
      (encPair (blockEnc Γ) (encOption (blockEnc Δ))) encBool := by
  let E := encPair (blockEnc Γ) (encOption (blockEnc Δ))
  have hfst : ComputableInPolyTime (fun q : (List Γ × Option (List Δ)) × List Δ => q.1.1)
      (encPair E (blockEnc Δ)) (blockEnc Γ) :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
  have hsnd : ComputableInPolyTime (fun q : (List Γ × Option (List Δ)) × List Δ => q.2)
      (encPair E (blockEnc Δ)) (blockEnc Δ) := ComputableInPolyTime.snd _ _
  have hlen : ComputableInPolyTime
      (fun q : (List Γ × Option (List Δ)) × List Δ => decide (q.2.length ≤ q.1.1.length ^ k))
      (encPair E (blockEnc Δ)) encBool :=
    ComputableInPolyTime.unary_le.comp
      (((ComputableInPolyTime.length (encFinite Δ)).comp hsnd).prod
        ((ComputableInPolyTime.unary_pow k).comp
          ((ComputableInPolyTime.length (encFinite Γ)).comp hfst)))
  have hbody := ComputableInPolyTime.bool_and' hlen (hf.comp (hfst.prod hsnd))
  exact ComputableInPolyTime.optionElimWithInput (ComputableInPolyTime.snd _ _)
    (ComputableInPolyTime.const false) hbody

/-- **Clay NP to cslib-frontier NP.** -/
theorem mem_NP_of_inNP {L : Millennium.Language (List Γ)}
    (h : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Γ) L) :
    {w | L w} ∈ NP (blockEnc Γ) := by
  obtain ⟨Δ, _, R, k, ⟨f, hf, hfR⟩, hL⟩ := h
  -- The Clay checker, as a cslib-frontier function on pairs.
  have hfc : ComputableInPolyTime f
      ((⟨pairWord, pairWord_injective⟩ : List Γ × List Δ ↪ _).trans (blockEnc (Γ ⊕ Option Δ)))
      encBool :=
    computableInPolyTime_of_tm2 pairWord_injective
      (hf : TM2ComputableInPolyTime pairWord (fun b : Bool => [b]) f)
  have hid : ComputableInPolyTime (fun p : List Γ × List Δ => p)
      (encPair (blockEnc Γ) (blockEnc Δ))
      ((⟨pairWord, pairWord_injective⟩ : List Γ × List Δ ↪ _).trans (blockEnc (Γ ⊕ Option Δ))) :=
    pairWord_polyTime.of_enc_eq fun _ => rfl
  have hfp : ComputableInPolyTime f (encPair (blockEnc Γ) (blockEnc Δ)) encBool := hfc.comp hid
  refine mem_NP_of_check (p := Polynomial.C (2 * Nat.card Δ + 1) * Polynomial.X ^ k + 1)
    (certDecoder Δ) (clayCheck_polyTime k hfp) ?sound ?complete
  case sound =>
    rintro a (_ | y) hc
    · simp [clayCheck] at hc
    · simp only [clayCheck, Option.elim_some, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact (hL a).mpr ⟨y, hc.1, (hfR (a, y)).mpr hc.2⟩
  case complete =>
    intro a ha
    obtain ⟨y, hy, hR⟩ := (hL a).mp ha
    refine ⟨some y, ?_, ?_⟩
    · simp only [clayCheck, Option.elim_some, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hy, (hfR (a, y)).mp hR⟩
    · change (true :: blockEnc Δ y).length ≤ _
      have h₁ := length_blockEnc_le Δ y
      have h₂ : a.length ^ k ≤ (blockEnc Γ a).length ^ k :=
        Nat.pow_le_pow_left (length_le_blockEnc Γ a) k
      have h₃ : y.length ≤ (blockEnc Γ a).length ^ k := hy.trans h₂
      simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      nlinarith

end ClayToCslib

section Bounds

theorem eval_le_mul_pow (q : Polynomial ℕ) {x : ℕ} (hx : 1 ≤ x) :
    q.eval x ≤ q.eval 1 * x ^ q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

/-- A polynomial in a length that is at most `C n` is at most `n ^ k` once `n ≥ 2`. -/
theorem exists_pow_bound (q : Polynomial ℕ) (C : ℕ) :
    ∃ k, ∀ n x, 2 ≤ n → 1 ≤ x → x ≤ C * n → q.eval x ≤ n ^ k := by
  refine ⟨q.eval 1 * C ^ q.natDegree + q.natDegree, fun n x hn hx hxC => ?_⟩
  calc q.eval x ≤ q.eval 1 * x ^ q.natDegree := eval_le_mul_pow q hx
    _ ≤ q.eval 1 * (C * n) ^ q.natDegree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxC _)
    _ = (q.eval 1 * C ^ q.natDegree) * n ^ q.natDegree := by rw [mul_pow]; ring
    _ ≤ 2 ^ (q.eval 1 * C ^ q.natDegree) * n ^ q.natDegree :=
        Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ ≤ n ^ (q.eval 1 * C ^ q.natDegree) * n ^ q.natDegree :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn _)
    _ = n ^ (q.eval 1 * C ^ q.natDegree + q.natDegree) := (pow_add _ _ _).symm

end Bounds

section CslibToClay

open Classical in
/-- The words of length at most one. -/
noncomputable def shortWords (Γ : Type) [Fintype Γ] : List (List Γ) :=
  [] :: (Finset.univ : Finset Γ).toList.map fun s => [s]

theorem mem_shortWords {Γ : Type} [Fintype Γ] {a : List Γ} (ha : a.length ≤ 1) :
    a ∈ shortWords Γ := by
  match a, ha with
  | [], _ => simp [shortWords]
  | [s], _ => simp [shortWords]

open Classical in
/-- The members of `A` of length at most one. -/
noncomputable def shortMembers {Γ : Type} [Fintype Γ] (A : Set (List Γ)) : List (List Γ) :=
  (shortWords Γ).filter fun w => decide (w ∈ A)

theorem mem_shortMembers {Γ : Type} [Fintype Γ] {A : Set (List Γ)} {a : List Γ}
    (ha : a.length ≤ 1) : a ∈ shortMembers A ↔ a ∈ A := by
  classical
  simp [shortMembers, mem_shortWords ha]

variable {Γ : Type} [Fintype Γ]

open Classical in
/-- The Clay checking relation built from a cslib-frontier verifier `V` with length `q`. Words of
length at most one take the empty certificate and are checked by table lookup. -/
noncomputable def cslibCheck (A : Set (List Γ)) (q : Polynomial ℕ) (V : List Γ × List Bool → Bool)
    (x : List Γ × List Bool) : Bool :=
  if x.1.length ≤ 1 then decide (x.2.length ≤ 0) && decide (x.1 ∈ shortMembers A)
  else decide (x.2.length ≤ q.eval (blockEnc Γ x.1).length) &&
    decide (q.eval (blockEnc Γ x.1).length ≤ x.2.length) && V x

theorem cslibCheck_polyTime (A : Set (List Γ)) (q : Polynomial ℕ) {V : List Γ × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (blockEnc Γ) encBits) encBool) :
    ComputableInPolyTime (cslibCheck A q V) (encPair (blockEnc Γ) encBits) encBool := by
  classical
  let E := encPair (blockEnc Γ) encBits
  have hfst : ComputableInPolyTime (fun x : List Γ × List Bool => x.1) E (blockEnc Γ) :=
    ComputableInPolyTime.fst _ _
  have hsnd : ComputableInPolyTime (fun x : List Γ × List Bool => x.2) E encBits :=
    ComputableInPolyTime.snd _ _
  have hl₁ : ComputableInPolyTime (fun x : List Γ × List Bool => x.1.length) E encUnary :=
    (ComputableInPolyTime.length (encFinite Γ)).comp hfst
  have hl₂ : ComputableInPolyTime (fun x : List Γ × List Bool => x.2.length) E encUnary :=
    ComputableInPolyTime.length_bits.comp hsnd
  have hq : ComputableInPolyTime (fun x : List Γ × List Bool => q.eval (blockEnc Γ x.1).length)
      E encUnary :=
    (ComputableInPolyTime.unary_eval q).comp
      ((ComputableInPolyTime.encoding_length (blockEnc Γ)).comp hfst)
  have hc : ComputableInPolyTime (fun x : List Γ × List Bool => decide (x.1.length ≤ 1)) E encBool :=
    ComputableInPolyTime.unary_le.comp (hl₁.prod (ComputableInPolyTime.const 1))
  have hyes : ComputableInPolyTime
      (fun x : List Γ × List Bool => decide (x.2.length ≤ 0) && decide (x.1 ∈ shortMembers A))
      E encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.unary_le.comp (hl₂.prod (ComputableInPolyTime.const 0)))
      (ComputableInPolyTime.decide_mem (ComputableInPolyTime.const _) hfst)
  have hno : ComputableInPolyTime
      (fun x : List Γ × List Bool => decide (x.2.length ≤ q.eval (blockEnc Γ x.1).length) &&
        decide (q.eval (blockEnc Γ x.1).length ≤ x.2.length) && V x) E encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.unary_le.comp (hl₂.prod hq))
        (ComputableInPolyTime.unary_le.comp (hq.prod hl₂)))
      hV
  exact ComputableInPolyTime.ite_decide hc hyes hno

/-- **cslib-frontier NP to Clay NP.** -/
theorem inNP_of_mem_NP [Nonempty Γ] {L : Millennium.Language (List Γ)}
    (h : {w | L w} ∈ NP (blockEnc Γ)) :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Γ) L := by
  classical
  have : Inhabited Γ := Classical.inhabited_of_nonempty'
  obtain ⟨q, V, hV, hver⟩ := h
  obtain ⟨k, hk⟩ := exists_pow_bound q (2 * Nat.card Γ + 1)
  let g := cslibCheck {w | L w} q V
  let R : List Γ → List Bool → Prop := fun a y => g (a, y) = true
  -- The Clay checker is polynomial-time on the pair word.
  have hg := cslibCheck_polyTime {w | L w} q hV
  have hpw : ComputableInPolyTime (pairWord : List Γ × List Bool → _)
      ((⟨pairWord, pairWord_injective⟩ : List Γ × List Bool ↪ _).trans
        (blockEnc (Γ ⊕ Option Bool))) (blockEnc (Γ ⊕ Option Bool)) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hbits : ComputableInPolyTime (fun y : List Bool => y) (blockEnc Bool) encBits :=
    (trans_encList_polyTime encBits (encFinite Bool)).2
  have hconv : ComputableInPolyTime (fun x : List Γ × List Bool => x)
      (encPair (blockEnc Γ) (blockEnc Bool)) (encPair (blockEnc Γ) encBits) :=
    (ComputableInPolyTime.fst _ _).prod (hbits.comp (ComputableInPolyTime.snd _ _))
  have hgc := (hg.comp hconv).comp (unpair_polyTime.comp hpw)
  have heq : ((g ∘ fun x => x) ∘ (fun s => (lefts s, rights s)) ∘ pairWord) = g := by
    funext x
    simp [lefts_pairWord, rights_pairWord]
  rw [heq] at hgc
  obtain ⟨cert⟩ := tm2_of_computableInPolyTime pairWord_injective hgc
  refine ⟨Bool, inferInstance, R, k, ⟨g, cert, fun _ => Iff.rfl⟩, fun a => ?_⟩
  change L a ↔ ∃ y : List Bool, y.length ≤ a.length ^ k ∧ g (a, y) = true
  by_cases ha : a.length ≤ 1
  · have hg' : ∀ y : List Bool, g (a, y) = true ↔ y = [] ∧ L a := by
      intro y
      simp only [g, cslibCheck, if_pos ha, Bool.and_eq_true, decide_eq_true_eq,
        mem_shortMembers ha, Nat.le_zero, List.length_eq_zero_iff]
      rfl
    simp only [hg']
    exact ⟨fun hL => ⟨[], by simp, rfl, hL⟩, fun ⟨_, _, _, hL⟩ => hL⟩
  · have hg' : ∀ y : List Bool, g (a, y) = true ↔
        y.length = q.eval (blockEnc Γ a).length ∧ V (a, y) = true := by
      intro y
      simp only [g, cslibCheck, if_neg ha, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨le_antisymm h₁ h₂, h₃⟩
      · rintro ⟨h₁, h₃⟩; exact ⟨⟨h₁.le, h₁.ge⟩, h₃⟩
    simp only [hg']
    have hmem : L a ↔ ∃ w : List Bool, w.length = q.eval (blockEnc Γ a).length ∧ V (a, w) = true :=
      hver a
    rw [hmem]
    constructor
    · rintro ⟨w, hw, hVw⟩
      refine ⟨w, ?_, hw, hVw⟩
      rw [hw]
      exact hk a.length _ (by omega) ((by omega : 1 ≤ a.length).trans (length_le_blockEnc Γ a))
        (length_blockEnc_le Γ a)
    · rintro ⟨w, -, hw, hVw⟩
      exact ⟨w, hw, hVw⟩

end CslibToClay

variable (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ))

/-- **L2 for NP.** A language over a finite alphabet with at least two symbols is in Clay's NP
exactly when it is in cslib-frontier's NP under the block code. -/
theorem clayNP_iff_cslib :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Γ) L ↔
      {w | L w} ∈ NP (blockEnc Γ) :=
  ⟨mem_NP_of_inNP, inNP_of_mem_NP⟩

end Monteverde
