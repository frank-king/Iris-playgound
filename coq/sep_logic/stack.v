(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.

(* Allows to use points-to predicate. *)
Context `{!heapGS Σ}.

Notation iProp := (iProp Σ).

Section exercise4_35.
  Axiom mk_stack: val.
  Axiom push: val.
  Axiom pop: val.

  Definition stack_spec_def :=
    ∃ (is_stack : val → list val → iProp),
    {{{ True }}} mk_stack #() {{{ s, RET s; is_stack s [] }}} ∧
    (∀ s x xs,
      {{{ is_stack s xs }}}
        push x s
      {{{ RET #(); is_stack s (x :: xs) }}}) ∧
    (∀ s x xs,
      {{{ is_stack s (x :: xs) }}}
        pop s
      {{{ RET SOMEV x; is_stack s xs }}}).

  Definition prog4_35: expr :=
    let: "s" := mk_stack #() in
      push #1 "s";; push #2 "s";; pop "s";; pop "s".

  Lemma prog4_35_spec :
    stack_spec_def →
      {{{ True }}} prog4_35 {{{ RET SOMEV #1; True }}}.
  Proof.
    intros (is_stack & Hmk & Hpush & Hpop).
    iIntros (Φ) "_ H". unfold prog4_35. wp_bind (mk_stack _).
    wp_apply (Hmk); [done|]. iIntros (s) "Hs". wp_let.
    do 2 (
      wp_apply (Hpush with "[$] [H]"); iNext; iIntros "Hs"; wp_seq
    ).
    do 2 (
      wp_apply (Hpop with "[$] [H]"); iNext; iIntros "Hs"; try wp_seq
    ).
    by iApply "H".
  Qed.
End exercise4_35.

Section exercise4_36.
  Definition stackP_spec_def :=
    ∃ (is_stack : val → list (val → iProp) → iProp),
    {{{ True }}} mk_stack #() {{{ s, RET s; is_stack s [] }}} ∧
    (∀ s ϕ ϕs x,
      {{{ is_stack s ϕs ∗ ϕ x}}}
        push x s
      {{{ RET #(); is_stack s (ϕ :: ϕs) }}}) ∧
    (∀ s ϕ ϕs x,
      {{{ is_stack s (ϕ :: ϕs) }}}
        pop s
      {{{ RET SOMEV x; ϕ x ∗ is_stack s ϕs }}}).

  Lemma stack_spec_from_stackP_spec_axiom :
    stackP_spec_def → stack_spec_def.
  Proof.
    intros (is_stack & Hmk & Hpush & Hpop).
    exists (fun s xs => is_stack s ((fun _ _ => True%I) <$> xs)).
    split.
    - iIntros (Φ) "_ H". by wp_apply (Hmk).
    - split; iIntros (s x xs Φ) "Hs H".
      + iAssert (True%I) as "I"; [done|].
        wp_apply (Hpush with "[Hs] [H]"); [by iFrame|]. iNext.
        iApply "H".
      + wp_apply (Hpop with "[$] [H]"). iNext.
        iIntros "[_ Hs]". by iApply "H".
  Qed.
End exercise4_36.

Section exercise4_37.
  Definition prog4_37: expr :=
    let: "s" := mk_stack #() in
    let: "x1" := ref #1 in
    let: "x2" := ref #2 in
    push "x1" "s";; push "x2" "s";; pop "s";;
    let: "y" := pop "s" in
      match: "y" with
        NONE => #()
      | SOME "l" => ! "l"
      end.

  Lemma prog4_37_spec :
    stackP_spec_def →
      {{{ True }}} prog4_37 {{{ RET #1; True }}}.
  Proof.
    intros (is_stack & Hmk & Hpush & Hpop).
    iIntros (Φ) "_ H". unfold prog4_37.
    wp_apply (Hmk with "[$] [H]"). iNext.
    iIntros (s) "Hs". wp_let.

    wp_alloc l1 as "Hx1". wp_let. remember #l1 as v1.
    wp_alloc l2 as "Hx2". wp_let. remember #l2 as v2.

    wp_apply (Hpush with "[Hx1 Hs] [H Hx2]"); [by iFrame|]. iNext.
    iIntros "Hs". wp_seq.

    wp_apply (Hpush with "[Hx2 Hs] [H]"); [by iFrame|]. iNext.
    iIntros "Hs". wp_seq.

    wp_bind (pop _).
    wp_apply (Hpop with "[$Hs] [H]"). iNext.
    iIntros "[Hx2 Hs]". wp_seq.

    wp_apply (Hpop with "[$Hs] [H Hx2]"). iNext.
    iIntros "[Hx1 Hs]". wp_let.

    wp_match. wp_load. by iApply "H".
    Unshelve. done.
  Qed.
End exercise4_37.

Section exercise4_38.
  Definition stackP'_spec_def :=
    ∃ (is_stack : val → list val → (val → iProp) → iProp),
    ∀ ϕ : val → iProp,
    {{{ True }}} mk_stack #() {{{ s, RET s; is_stack s [] ϕ }}} ∧
    (∀ s x xs,
      {{{ is_stack s xs ϕ ∗ ϕ x}}}
        push x s
      {{{ RET #(); is_stack s (x :: xs) ϕ }}}) ∧
    (∀ s x xs,
      {{{ is_stack s (x :: xs) ϕ }}}
        pop s
      {{{ RET SOMEV x; ϕ x ∗ is_stack s xs ϕ }}}).

  Fixpoint ϕs (ϕ : val → iProp) (xs : list val) :=
    match xs with
    | [] => []
    | x :: xs => ϕ :: ϕs ϕ xs
    end.

  Lemma stackP'_spec_from_stackP_spec :
    stackP_spec_def → stackP'_spec_def.
  Proof.
    intros (is_stack & Hmk & Hpush & Hpop).
    exists (fun s xs ϕ => is_stack s (ϕs ϕ xs)). split.
    - iIntros (Φ) "_ H". by wp_apply (Hmk).
    - split; iIntros (s x xs Φ) "Hs H".
      + wp_apply (Hpush with "[$] [H]"). iNext.
        iIntros "Hs". by iApply "H".
      + wp_apply (Hpop with "[$] [H]"). iNext.
        iIntros "[Hϕ Hs]". iApply "H". iFrame.
  Qed.
End exercise4_38.
