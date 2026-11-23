/-
Alpöge's Certified Lean Derivation Does Not Prove the Riemann Hypothesis:
Granting Every Check, the Hypothesis Follows from a Premise Stronger Than Itself

Parker Emmerson (Yaohushuason), November 2026.

The statements of the note that concern the prover's own rules, checked in the core of
Lean 4.33.1, the version to which the certified archive is pinned. The file imports
nothing beyond the prover's prelude. Each declaration names the statement of the note
that it checks; the last lines print the axioms on which each declaration rests.
-/

namespace CompletenessOfValues

universe u

/-! ## Terms completed by clause in the prover's core
    (the proposition "The clauses, and the term of the certified sentence") -/

/-- Division of natural numbers is completed at the divisor "0" by the value "0". -/
theorem nat_div_completed (n : Nat) : n / 0 = 0 := Nat.div_zero n

/-- The remainder is completed at the divisor "0" by the dividend. -/
theorem nat_mod_completed (n : Nat) : n % 0 = n := Nat.mod_zero n

/-- Subtraction of natural numbers is completed, where the subtrahend is the larger, by "0". -/
theorem nat_sub_completed : (2 : Nat) - 5 = 0 := rfl

/-- The predecessor is completed at "0" by "0". -/
theorem nat_pred_completed : Nat.pred 0 = 0 := rfl

/-! ## Statements: `False`, the counter-inscription, and "apart from" -/

/-- The counter-inscription of a statement is, by definition, "the statement yields `False`". -/
theorem counter_inscription_unfolds (a : Prop) : (¬ a) = (a → False) := rfl

/-- "Apart from" is, by definition, "equality yields `False`". -/
theorem apart_unfolds {α : Sort u} (x y : α) : (x ≠ y) = (x = y → False) := rfl

/-- `False` has no rule of derivation: a case analysis on a derivation of it has no case,
and so yields every statement. -/
theorem false_has_no_case (h : False) (q : Prop) : q := nomatch h

/-! ## Every statement is decided in value
    (the theorem "Every statement is decided in value") -/

/-- Part (1): the prover's own theorem `Classical.propComplete`. -/
theorem decided_in_value (a : Prop) : a = True ∨ a = False := Classical.propComplete a

/-- Part (2): the excluded middle derived from the selection axiom, by the argument of
Diaconescu (1975), written step by step. The prover's core library proves the same statement
by the same argument (`Classical.em`). -/
theorem excluded_middle_from_selection (p : Prop) : p ∨ ¬ p := by
  -- Two collections of statements: `U` holds of `True`, `V` holds of `False`, and both hold
  -- of every statement when `p` holds.
  let U : Prop → Prop := fun x => x = True ∨ p
  let V : Prop → Prop := fun x => x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  -- The selection axiom issues a member of each collection.
  have hu : U (Classical.choose exU) := Classical.choose_spec exU
  have hv : V (Classical.choose exV) := Classical.choose_spec exV
  -- If `p` holds, the two collections are one collection, by function extensionality and
  -- propositional extensionality, and the selection issues one member for both.
  have same : p → Classical.choose exU = Classical.choose exV := by
    intro hp
    have hUV : U = V :=
      funext fun x => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    have key : ∀ (W : Prop → Prop) (e : U = W) (ex : ∃ x, W x),
        Classical.choose exU = Classical.choose ex := by
      intro W e
      subst e
      intro ex
      rfl
    exact key V hUV exV
  -- The cases.
  cases hu with
  | inr hp => exact Or.inl hp
  | inl huT =>
    cases hv with
    | inr hp => exact Or.inl hp
    | inl hvF =>
      refine Or.inr (fun hp => ?_)
      have e : True = False := huT.symm.trans ((same hp).trans hvF)
      exact e.mp True.intro

/-- From the excluded middle and propositional extensionality, the value of every statement. -/
theorem decided_in_value_from_selection (a : Prop) : a = True ∨ a = False :=
  match excluded_middle_from_selection a with
  | Or.inl h => Or.inl (propext ⟨fun _ => True.intro, fun _ => h⟩)
  | Or.inr h => Or.inr (propext ⟨fun ha => h ha, fun hf => nomatch hf⟩)

/-- Part (3): the rules define a function from the statements to the two values. The prover
requires the mark `noncomputable`: the function is defined and no program computes it. -/
noncomputable def value (a : Prop) : Bool := @decide a (Classical.propDecidable a)

theorem value_true_iff (a : Prop) : value a = true ↔ a := by
  unfold value
  exact @decide_eq_true_iff a (Classical.propDecidable a)

theorem value_false_iff (a : Prop) : value a = false ↔ ¬ a := by
  unfold value
  exact @decide_eq_false_iff_not a (Classical.propDecidable a)

/-- Every statement receives one of the two values. -/
theorem value_total (a : Prop) : value a = true ∨ value a = false :=
  match value a with
  | true => Or.inl rfl
  | false => Or.inr rfl

/-! ## Formation data, completions, and the raw sentence
    (the section "The certified derivation is not a derivation from the zeta series") -/

/-- The shape of the classical sentence: positions, values, the region on which a clause
presents values, a strip, a line, the clause, and the constant of the matrix. -/
structure Formation where
  Pos : Type
  Val : Type
  presented : Pos → Prop
  strip : Pos → Prop
  line : Pos → Prop
  clause : (s : Pos) → presented s → Val
  z : Val

/-- A completion agrees with the clause wherever the clause presents a value. -/
def IsCompletion (F : Formation) (f : F.Pos → F.Val) : Prop :=
  ∀ (s : F.Pos) (h : F.presented s), f s = F.clause s h

/-- The raw sentence at a function: every position of the strip at which the function issues
the constant of the matrix lies on the line. -/
def Raw (F : Formation) (f : F.Pos → F.Val) : Prop :=
  ∀ s : F.Pos, F.strip s → f s = F.z → F.line s

/-- The three facts: the clause withholds its value on the strip; the strip has a position off
the line; and a value apart from the constant of the matrix exists. -/
structure Facts (F : Formation) : Prop where
  strip_withheld : ∀ s, F.strip s → ¬ F.presented s
  off_line : ∃ p, F.strip p ∧ ¬ F.line p
  other_value : ∃ u : F.Val, u ≠ F.z

/-- The completion that issues `w` wherever the clause withholds a value. -/
noncomputable def fill (F : Formation) (w : F.Pos → F.Val) : F.Pos → F.Val :=
  fun s => @dite F.Val (F.presented s) (Classical.propDecidable _) (fun h => F.clause s h) (fun _ => w s)

theorem fill_isCompletion (F : Formation) (w : F.Pos → F.Val) : IsCompletion F (fill F w) := by
  intro s h
  unfold fill
  exact @dif_pos (F.presented s) (Classical.propDecidable _) h F.Val _ _

theorem fill_off (F : Formation) (w : F.Pos → F.Val) (s : F.Pos) (h : ¬ F.presented s) :
    fill F w s = w s := by
  unfold fill
  exact @dif_neg (F.presented s) (Classical.propDecidable _) h F.Val _ _

/-- The theorem "The formation data give the sentence both truth values", part (1): one
completion makes the raw sentence true and another makes it false. -/
theorem both_values {F : Formation} (hF : Facts F) :
    (∃ f, IsCompletion F f ∧ Raw F f) ∧ (∃ g, IsCompletion F g ∧ ¬ Raw F g) := by
  obtain ⟨u, hu⟩ := hF.other_value
  obtain ⟨p, hp, hpl⟩ := hF.off_line
  refine ⟨⟨fill F (fun _ => u), fill_isCompletion F _, ?_⟩,
          ⟨fill F (fun _ => F.z), fill_isCompletion F _, ?_⟩⟩
  · intro s hs hz
    have e : fill F (fun _ => u) s = u := fill_off F _ s (hF.strip_withheld s hs)
    exact absurd (e.symm.trans hz) hu
  · intro h
    have e : fill F (fun _ => F.z) p = F.z := fill_off F _ p (hF.strip_withheld p hp)
    exact hpl (h p hp e)

/-- A system of rules derives properties of functions; it is sound for the completions when
whatever it derives holds at every completion. -/
structure System (F : Formation) where
  derives : ((F.Pos → F.Val) → Prop) → Prop

def System.Sound {F : Formation} (S : System F) : Prop :=
  ∀ φ, S.derives φ → ∀ f, IsCompletion F f → φ f

/-- The same theorem, part (2): every system of rules sound for the completions leaves the raw
sentence and its counter-inscription both underived. -/
theorem underived_from_formation_data {F : Formation} (hF : Facts F) (S : System F)
    (hS : S.Sound) : ¬ S.derives (Raw F) ∧ ¬ S.derives (fun f => ¬ Raw F f) := by
  obtain ⟨⟨f, hf, hfr⟩, ⟨g, hg, hgr⟩⟩ := both_values hF
  exact ⟨fun h => hgr (hS _ h g hg), fun h => hS _ h f hf hfr⟩

/-- The theorem "The analytic selection", the abstract part: when an admissibility clause leaves
one completion, every admissible completion gives the raw sentence the same truth value. -/
theorem selection_fixes {F : Formation} (adm : (F.Pos → F.Val) → Prop)
    (one : ∀ f g, IsCompletion F f → IsCompletion F g → adm f → adm g → f = g)
    (f g : F.Pos → F.Val) (hf : IsCompletion F f) (hg : IsCompletion F g)
    (af : adm f) (ag : adm g) : Raw F f ↔ Raw F g := by
  rw [one f g hf hg af ag]

/-- The corollary "The value before the derivation": at every function the raw sentence is
decided in value, by one application of `decided_in_value`; the derivation supplies neither of
the two values. -/
theorem selected_sentence_has_value {F : Formation} (f : F.Pos → F.Val) :
    Raw F f = True ∨ Raw F f = False :=
  decided_in_value (Raw F f)

/-! ## Refutation, presentation, and Markov's principle
    (the theorem "Refutation, presented bound, and Markov's principle") -/

/-- Markov's principle: a sequence of decisions that is refuted to fail at every place
succeeds at some place. -/
def MarkovPrinciple : Prop :=
  ∀ d : Nat → Bool, ¬ (∀ n, d n = false) → ∃ n, d n = true

/-- The certificate passage: at every window, a search whose failure at every candidate is
refuted finds a certificate. -/
def CertificatePassage : Prop :=
  ∀ cert : Nat → Nat → Bool, (∀ w, ¬ ∀ c, cert w c = false) → ∀ w, ∃ c, cert w c = true

/-- The certificate passage is Markov's principle. -/
theorem certificate_passage_iff_markov : CertificatePassage ↔ MarkovPrinciple :=
  ⟨fun hP d hd => hP (fun _ c => d c) (fun _ => hd) 0, fun hM cert h w => hM (cert w) (h w)⟩

/-- In the completed rules Markov's principle is a theorem: the excluded middle supplies it. -/
theorem markov_in_completed_rules : MarkovPrinciple := by
  intro d h
  apply Classical.byContradiction
  intro hne
  apply h
  intro n
  cases hd : d n with
  | false => rfl
  | true => exact absurd ⟨n, hd⟩ hne

/-- `Halts d n`: the search that tests `d` at `n`, `n + 1`, and so on, stops. Its one rule:
the search stops from `n` when, if `d` fails at `n`, the search stops from `n + 1`. -/
inductive Halts (d : Nat → Bool) : Nat → Prop
  | step (n : Nat) (h : d n = false → Halts d (n + 1)) : Halts d n

theorem Halts.next {d : Nat → Bool} {n : Nat} (h : Halts d n) (hd : d n = false) :
    Halts d (n + 1) :=
  match h with
  | .step _ f => f hd

theorem halts_before (d : Nat → Bool) (m : Nat) (hm : d m = true) :
    ∀ k n, n + k = m → Halts d n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have e : n = m := hn
    subst e
    exact Halts.step n (fun hf => Bool.noConfusion (hm.symm.trans hf))
  | succ k ih =>
    intro n hn
    exact Halts.step n
      (fun _ => ih (n + 1) (by rw [Nat.add_assoc, Nat.add_comm 1 k]; exact hn))

/-- An existence statement yields that the search from the first place stops. -/
theorem halts_of_exists (d : Nat → Bool) (h : ∃ n, d n = true) : Halts d 0 :=
  match h with
  | ⟨m, hm⟩ => halts_before d m hm m 0 (Nat.zero_add m)

/-- One step of the search, as a relation on the places from which the search stops. -/
def Step (d : Nat → Bool) (a b : { n : Nat // Halts d n }) : Prop :=
  a.1 = b.1 + 1 ∧ d b.1 = false

theorem step_wf (d : Nat → Bool) : WellFounded (Step d) := by
  constructor
  intro a
  obtain ⟨n, h⟩ := a
  induction h with
  | step n f ih =>
    constructor
    intro b hb
    obtain ⟨m, hm⟩ := b
    obtain ⟨e, hf⟩ := hb
    have e' : m = n + 1 := e
    subst e'
    exact ih hf

instance (d : Nat → Bool) : WellFoundedRelation { n : Nat // Halts d n } where
  rel := Step d
  wf := step_wf d

/-- The search: test `d` at the place; stop there if it succeeds; otherwise go on. -/
def searchFrom (d : Nat → Bool) (a : { n : Nat // Halts d n }) : { m : Nat // d m = true } :=
  match hd : d a.1 with
  | true => ⟨a.1, hd⟩
  | false => searchFrom d ⟨a.1 + 1, a.2.next hd⟩
termination_by a
decreasing_by exact ⟨rfl, hd⟩

/-- From an existence statement to a presented number, by the search. No axiom is used. -/
def present (d : Nat → Bool) (h : ∃ n, d n = true) : { m : Nat // d m = true } :=
  searchFrom d ⟨0, halts_of_exists d h⟩

/-- From a refutation to a presented number: Markov's principle, then the search. -/
def presentFromRefutation (d : Nat → Bool) (h : ¬ ∀ n, d n = false) :
    { m : Nat // d m = true } :=
  present d (markov_in_completed_rules d h)

/-- A demonstration: the decision that succeeds at the number 7 and at no other. -/
def demo : Nat → Bool := fun n => n == 7

theorem demo_refuted : ¬ ∀ n, demo n = false :=
  fun h => Bool.noConfusion ((h 7).symm.trans (rfl : demo 7 = true))

/-! ## A clause read backwards, and the excluded middle
    (the theorem "The backward reading of a clause is the excluded middle") -/

/-- An operation completed by a clause. Where the rule presents a value (the statement `P`
holds, and the value is `rule h`), the operation issues that value; elsewhere it issues the
default `d`. The library's integral has this shape, with `P` the statement that the function
is integrable and `d` the value "0". The prover requires the mark `noncomputable`. -/
noncomputable def completed {α : Type} (P : Prop) (rule : P → α) (d : α) : α :=
  @dite α P (Classical.propDecidable P) (fun h => rule h) (fun _ => d)

/-- Where the rule presents a value, the completed operation issues it. -/
theorem completed_presented {α : Type} (P : Prop) (rule : P → α) (d : α) (h : P) :
    completed P rule d = rule h := by
  unfold completed
  exact @dif_pos P (Classical.propDecidable P) h α _ _

/-- The clause: where the rule withholds a value, the completed operation issues the default. -/
theorem completed_clause {α : Type} (P : Prop) (rule : P → α) (d : α) (h : ¬ P) :
    completed P rule d = d := by
  unfold completed
  exact @dif_neg P (Classical.propDecidable P) h α _ _

/-- The clause read backwards, in the completed rules: if the completed operation issues a
value apart from the default, then the rule presents a value. This is the inference of the
library's lemma `Integrable.of_integral_ne_zero`. -/
theorem presented_of_apart {α : Type} (P : Prop) (rule : P → α) (d : α)
    (h : completed P rule d ≠ d) : P :=
  Classical.byContradiction (fun hn => h (completed_clause P rule d hn))

/-- Without the excluded middle, a clause and a value apart from the default give the
refutation of the refutation of `P`, and no more. -/
theorem clause_gives_double_negation {α : Type} {P : Prop} {v d : α}
    (clause : ¬ P → v = d) (apart : v ≠ d) : ¬ ¬ P :=
  fun hn => apart (clause hn)

/-- The backward reading of a clause, as a schema over every type, every statement and every
pair of values: from "if `P` is refuted then `v = d`" and "`v` is apart from `d`", conclude `P`. -/
def BackwardReading : Prop :=
  ∀ (α : Type) (P : Prop) (v d : α), (¬ P → v = d) → v ≠ d → P

/-- The excluded middle, as a schema over every statement. -/
def ExcludedMiddle : Prop := ∀ p : Prop, p ∨ ¬ p

/-- The excluded middle yields the backward reading. -/
theorem backward_of_excluded_middle (em : ExcludedMiddle) : BackwardReading :=
  fun _ P _ _ clause apart =>
    match em P with
    | Or.inl h => h
    | Or.inr hn => absurd (clause hn) apart

/-- The backward reading, taken at the type of statements with the default `False`, removes a
double counter-inscription: the clause "if `q` is refuted then `q = False`" holds by
propositional extensionality, and `q` is apart from `False` when its refutation is refuted. -/
theorem double_negation_of_backward (B : BackwardReading) (q : Prop) (hnn : ¬ ¬ q) : q :=
  B Prop q q False
    (fun hn => propext ⟨fun hq => absurd hq hn, fun hf => False.elim hf⟩)
    (fun heq => hnn (fun hq => Eq.mp heq hq))

/-- The backward reading yields the excluded middle. -/
theorem excluded_middle_of_backward (B : BackwardReading) : ExcludedMiddle :=
  fun p => double_negation_of_backward B (p ∨ ¬ p)
    (fun h => h (Or.inr (fun hp => h (Or.inl hp))))

/-- The backward reading of a clause is the excluded middle. -/
theorem backward_reading_iff_excluded_middle : BackwardReading ↔ ExcludedMiddle :=
  ⟨excluded_middle_of_backward, backward_of_excluded_middle⟩

/-- In the completed rules the backward reading holds. -/
theorem backward_in_completed_rules : BackwardReading :=
  backward_of_excluded_middle Classical.em

/-! ## The sponsor of a derived law

`L` stands for "the law holds at every whole number" and `K` for "the rules are consistent."
What a certified derivation of the law establishes outright is the conditional `¬ L → ¬ K`:
a whole number at which the law failed would yield a clash. -/

/-- Proposition "A derived law over the whole numbers", the step: if each instance at which
`Q` held would yield a clash, then on the sponsor `K` the law holds. -/
theorem derived_law_on_sponsor {Q : Nat → Prop} {K : Prop}
    (clash : ∀ n, Q n → ¬ K) (hK : K) : ∀ n, ¬ Q n :=
  fun n hq => clash n hq hK

/-- The conditional excludes the fourth combination: the law fails and the rules are
consistent. -/
theorem excludes_fourth_case {L K : Prop} (h : ¬ L → ¬ K) : ¬ (¬ L ∧ K) :=
  fun hLK => h hLK.1 hLK.2

/-- The conditional holds in each of the first three combinations, so it excludes none of
them: the law and consistency; the law and a clash; no law and a clash. -/
theorem first_three_cases_admitted :
    (¬ True → ¬ True) ∧ (¬ True → ¬ False) ∧ (¬ False → ¬ False) :=
  ⟨fun h _ => h trivial, fun _ h => h, fun _ h => h⟩

/-- The conditional fails in the fourth combination. -/
theorem fourth_case_refuted : ¬ (¬ False → ¬ True) :=
  fun h => h (fun f => f) trivial

/-- The conditional is not the statement that exactly one of "the law" and "a clash" holds:
it admits the combination in which both hold. -/
theorem conditional_is_not_exclusive :
    ¬ (∀ L K : Prop, (¬ L → ¬ K) → ¬ (L ∧ ¬ K)) :=
  fun h => h True False (fun _ f => f) ⟨trivial, fun f => f⟩

/-- The step of the progression of sponsors: if no system of the progression derives its own
consistency, then none derives the consistency of all of them. Here `derives N n` reads "the
`N`-th system derives the consistency of the `n`-th." -/
theorem no_rung_closes (derives : Nat → Nat → Prop) (own : ∀ n, ¬ derives n n) :
    ¬ ∃ N, ∀ n, derives N n :=
  fun ⟨N, h⟩ => own N (h N)

/-! ## Löb's theorem, from the derivability conditions and one fixed point -/

/-- A system of derivation: formulas with a conditional `imp` and a formula `box a` read
"`a` is derived"; a relation `D` read "is derived"; the rule of detachment; the two schemes
of the conditional; and the three derivability conditions. -/
structure Derivability where
  Form : Type
  imp : Form → Form → Form
  box : Form → Form
  D : Form → Prop
  mp : ∀ {a b : Form}, D (imp a b) → D a → D b
  ax_k : ∀ a b : Form, D (imp a (imp b a))
  ax_s : ∀ a b c : Form, D (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  d1 : ∀ {a : Form}, D a → D (box a)
  d2 : ∀ a b : Form, D (imp (box (imp a b)) (imp (box a) (box b)))
  d3 : ∀ a : Form, D (imp (box a) (box (box a)))

namespace Derivability

variable (S : Derivability)

/-- Chaining two derived conditionals. -/
theorem chain {a b c : S.Form} (h1 : S.D (S.imp a b)) (h2 : S.D (S.imp b c)) :
    S.D (S.imp a c) :=
  S.mp (S.mp (S.ax_s a b c) (S.mp (S.ax_k (S.imp b c) a) h2)) h1

/-- From `a → (b → c)` and `a → b`, the conditional `a → c`. -/
theorem under {a b c : S.Form} (h1 : S.D (S.imp a (S.imp b c))) (h2 : S.D (S.imp a b)) :
    S.D (S.imp a c) :=
  S.mp (S.mp (S.ax_s a b c) h1) h2

/-- Theorem "Löb, 1955", the passage from the conditions and the fixed point: if
`box a → a` is derived, and `psi` is a fixed point of "if `box x` then `a`", then `a` is
derived. -/
theorem lob {a psi : S.Form}
    (fix1 : S.D (S.imp psi (S.imp (S.box psi) a)))
    (fix2 : S.D (S.imp (S.imp (S.box psi) a) psi))
    (h : S.D (S.imp (S.box a) a)) : S.D a :=
  have s1 : S.D (S.imp (S.box psi) (S.box (S.imp (S.box psi) a))) :=
    S.mp (S.d2 psi (S.imp (S.box psi) a)) (S.d1 fix1)
  have s2 : S.D (S.imp (S.box psi) (S.imp (S.box (S.box psi)) (S.box a))) :=
    S.chain s1 (S.d2 (S.box psi) a)
  have s3 : S.D (S.imp (S.box psi) (S.box a)) := S.under s2 (S.d3 psi)
  have s4 : S.D (S.imp (S.box psi) a) := S.chain s3 h
  have s5 : S.D psi := S.mp fix2 s4
  S.mp s4 (S.d1 s5)

/-- With the fixed point, `box a → a` is derived exactly when `a` is. -/
theorem lob_iff {a psi : S.Form}
    (fix1 : S.D (S.imp psi (S.imp (S.box psi) a)))
    (fix2 : S.D (S.imp (S.imp (S.box psi) a) psi)) :
    S.D (S.imp (S.box a) a) ↔ S.D a :=
  ⟨S.lob fix1 fix2, fun ha => S.mp (S.ax_k a (S.box a)) ha⟩

/-- The second incompleteness theorem as an instance: with `bot` for a clash, the formula
`box bot → bot` says that the system derives no clash, and a system that derives no clash
does not derive it. -/
theorem underived_consistency {bot psi : S.Form}
    (fix1 : S.D (S.imp psi (S.imp (S.box psi) bot)))
    (fix2 : S.D (S.imp (S.imp (S.box psi) bot) psi))
    (consistent : ¬ S.D bot) : ¬ S.D (S.imp (S.box bot) bot) :=
  fun h => consistent (S.lob fix1 fix2 h)

end Derivability

end CompletenessOfValues

open CompletenessOfValues

/-! ## The axiom report -/

#print axioms nat_div_completed
#print axioms nat_mod_completed
#print axioms nat_sub_completed
#print axioms nat_pred_completed
#print axioms counter_inscription_unfolds
#print axioms apart_unfolds
#print axioms false_has_no_case
#print axioms decided_in_value
#print axioms excluded_middle_from_selection
#print axioms decided_in_value_from_selection
#print axioms value
#print axioms value_true_iff
#print axioms value_false_iff
#print axioms value_total
#print axioms both_values
#print axioms underived_from_formation_data
#print axioms selection_fixes
#print axioms selected_sentence_has_value
#print axioms certificate_passage_iff_markov
#print axioms markov_in_completed_rules
#print axioms halts_of_exists
#print axioms step_wf
#print axioms searchFrom
#print axioms present
#print axioms presentFromRefutation
#print axioms completed
#print axioms completed_presented
#print axioms completed_clause
#print axioms presented_of_apart
#print axioms clause_gives_double_negation
#print axioms backward_of_excluded_middle
#print axioms double_negation_of_backward
#print axioms excluded_middle_of_backward
#print axioms backward_reading_iff_excluded_middle
#print axioms backward_in_completed_rules

#print axioms derived_law_on_sponsor
#print axioms excludes_fourth_case
#print axioms first_three_cases_admitted
#print axioms fourth_case_refuted
#print axioms conditional_is_not_exclusive
#print axioms no_rung_closes
#print axioms Derivability.chain
#print axioms Derivability.under
#print axioms Derivability.lob
#print axioms Derivability.lob_iff
#print axioms Derivability.underived_consistency

/-! ## The search, run -/

#eval (present demo ⟨7, rfl⟩).val
#eval (presentFromRefutation demo demo_refuted).val
