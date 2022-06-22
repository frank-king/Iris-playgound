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

Section exercise4_31.
  Definition mk_counter : val := λ: <>, ref #0%nat.
  Definition inc_counter : val := λ: "x", "x" <- ! "x" + #1.
  Definition read_counter : val := λ: "x", !"x".

  Lemma mk_counter_spec :
    {{{ True }}} mk_counter #() {{{ l, RET #l; l ↦ #0 }}}.
  Proof.
    iIntros (Φ) "_ H". wp_lam. wp_alloc l. iApply "H". by iFrame.
  Qed.

  Lemma inc_counter_spec l (n: nat) :
    {{{ l ↦ #n }}} inc_counter #l {{{ RET #(); l ↦ #(n + 1)%nat }}}.
  Proof.
    iIntros (Φ) "Hl H". wp_lam. wp_load. wp_op. wp_store.
    iApply "H".
    assert (H: (n + 1)%Z = (n + 1)%nat). { lia. } by rewrite H.
  Qed.

  Lemma read_counter_spec l (n: nat) :
    {{{ l ↦ #n }}} read_counter #l {{{ RET #n; l ↦ #n }}}.
  Proof.
    iIntros (Φ) "Hl H". wp_lam. wp_load. iApply "H". by iFrame.
  Qed.

  Lemma mk_inc_read_counter_spec :
    ∃ (C : val -> nat -> iProp),
    {{{ True }}} mk_counter #() {{{ c, RET c; C c 0 }}} ∧
    (∀ c (n : nat),
      {{{ C c n }}} inc_counter c {{{ RET #(); C c (n + 1) }}}) ∧
    (∀ c n,
      {{{ C c n }}} read_counter c {{{ RET #n; C c n }}}).
  Proof.
    exists (fun c n => (∃ (l: loc), ⌜c = #l⌝ ∗ l ↦ #n)%I).
    split.
    - iIntros (Φ) "_ H". wp_apply (mk_counter_spec); [done|].
      iIntros (l) "Hl". iApply "H". iExists l. by iFrame.
    - split; iIntros (c n Φ) "Hc H";
      iDestruct "Hc" as (l) "[%Hc Hl]"; subst;
      [wp_apply (inc_counter_spec with "[$] [H]")|
       wp_apply (read_counter_spec with "[$] [H]")];
      iNext; iIntros "Hl"; iApply "H"; iExists l; by iFrame.
  Qed.
End exercise4_31.

Section exercise4_32.
  Definition counter : val :=
    λ: <>, let: "x" := ref #0 in (
      λ: <>, "x" <- ! "x" + #1,
      λ: <>, ! "x"
    ).

  Lemma counter_spec :
    {{{ True }}}
      counter #()
    {{{ (inc read: val) (l: loc), RET (inc, read); l ↦ #0 ∗
      (∀ (n : nat),
        {{{ l ↦ #n }}} inc #() {{{ RET #(); l ↦ #(n + 1)%nat }}}) ∗
      (∀ (n : nat),
        {{{ l ↦ #n }}} read #() {{{ RET #n; l ↦ #n }}})
    }}}.
  Proof.
    iIntros (Φ) "_ H". wp_lam. wp_alloc l. wp_let. wp_pures.
    iApply "H". iFrame. iModIntro.
    iSplit; iIntros (n Φ'); iModIntro; iIntros "Hl H";
    wp_lam; wp_load; [wp_op; wp_store|]; iApply "H"; [| by iFrame].
    assert (H: (n + 1)%Z = (n + 1)%nat). { lia. } by rewrite H.
  Qed.
End exercise4_32.

Section exercise4_33.
  Definition counter_postcond (inc read : val): iProp :=
    ∃ (C: nat -> iProp), C 0 ∗
    (∀ n, {{{ C n }}} inc #() {{{ RET #(); C (n + 1) }}}) ∗
    (∀ n, {{{ C n }}} read #() {{{ RET #n; C n }}}).

  Lemma counter_spec_prop :
    {{{ True }}}
      counter #()
    {{{ inc read, RET (inc, read); counter_postcond inc read }}}.
  Proof.
    iIntros (Φ) "_ H". wp_lam. wp_alloc l. wp_let. wp_pures.
    iApply "H". iExists (fun n => (l ↦ #n)%I). iFrame. iModIntro.
    iSplit; iIntros (n Φ'); iModIntro; iIntros "Hl H";
    wp_lam; wp_load; [wp_op; wp_store|]; iApply "H"; [| by iFrame].
    assert (H: (n + 1)%Z = (n + 1)%nat). { lia. } by rewrite H.
  Qed.

  Lemma counter_spec_prop_from_counter_spec :
    {{{ True }}}
      counter #()
    {{{ (inc read : val), RET (inc, read);
      counter_postcond inc read }}}.
  Proof.
    iIntros (Φ) "_ H". wp_apply (counter_spec); [done|].
    iIntros (inc read l) "(Hl & Hinc & Hread)".
    iApply "H". iExists (fun n => (l ↦ #n)%I). iFrame.
  Qed.
End exercise4_33.

Section exercise4_34.
  Definition counter' : val :=
    λ: <>, let: "x" := mk_counter #() in (
      λ: <>, inc_counter "x",
      λ: <>, read_counter "x"
    ).

  Lemma counter_spec'_from_counter_spec_compound :
    {{{ True }}}
      counter' #()
    {{{ (inc read : val), RET (inc, read);
      counter_postcond inc read }}}.
  Proof.
    destruct (mk_inc_read_counter_spec) as (C & Hmk & Hinc & Hread).
    iIntros (Φ) "_ H". wp_lam. wp_bind (mk_counter _).
    wp_apply (Hmk); [done|]. iIntros (c) "Hc". wp_let. wp_pures.
    iApply "H". iExists (C c). iFrame. iModIntro.
    iSplit; iIntros (n Φ'); iModIntro; iIntros "Hc H"; wp_lam;
    [wp_apply (Hinc with "[$] [H]") |
     wp_apply (Hread with "[$] [H]")]; by iNext.
  Qed.
End exercise4_34.
