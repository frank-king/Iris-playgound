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
Implicit Types hd : loc.

Notation iProp := (iProp Σ).

Section exercise4_20.
  Fixpoint is_list (l: val) (xs: list val) : iProp :=
    match xs with
    | [] => ⌜l = NONEV⌝
    | x :: xs' => ∃ hd l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (x, l') ∗ is_list l' xs'
    end%I.

  Fixpoint is_list_nat (l: val) (xs: list Z) : iProp :=
    match xs with
    | [] => ⌜l = NONEV⌝
    | x :: xs' => ∃ hd l', ⌜l = SOMEV #hd⌝ ∗ hd ↦ (#x, l') ∗ is_list_nat l' xs'
    end%I.

  Definition inc : val :=
    rec: "inc" "l" :=
      match: "l" with
        NONE => #()
      | SOME "x2" =>
          let: "h" := Fst !"x2" in
          let: "t" := Snd !"x2" in
          "x2" <- (("h" + #1), "t");;
          "inc" "t"
      end.

  Lemma inc_spec l xs :
    {{{ is_list_nat l xs }}}
      inc l
    {{{ RET #(); is_list_nat l (List.map Z.succ xs) }}}.
  Proof.
    iIntros (ϕ) "Hxs H".
    iLöb as "IH" forall (l xs ϕ). wp_rec. destruct xs; iSimplifyEq.
    - wp_match. by iApply "H".
    - iDestruct "Hxs" as (hd l') "(% & Hx & Hxs)". iSimplifyEq.
      wp_match. do 2 (wp_load; wp_proj; wp_let). wp_op. wp_store.
      iApply ("IH" with "Hxs"). iNext. iIntros "Hl'".
      iApply "H". iExists hd, l'. by iFrame.
  Qed.
End exercise4_20.

Section exercise4_24.
  Definition append : val :=
    rec: "append" "l" "l'" :=
      match: "l" with
        NONE => "l'"
      | SOME "x2" =>
          let: "p" := ! "x2" in
          let: "r" := "append" (Snd "p") "l'" in
          "x2" <- ((Fst "p"), "r");;
          "l"
      end.

  Lemma append_spec l l' xs ys :
    {{{ is_list l xs ∗ is_list l' ys }}}
      append l l'
    {{{ v, RET v; is_list v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    iLöb as "IH" forall (l l' xs ys ϕ). wp_rec. wp_let.
    destruct xs; iSimplifyEq.
    - wp_match. by iApply "H".
    - iDestruct "Hxs" as (hd l1) "(% & Hx & Hxs)". subst.
      wp_match. wp_load. wp_let. wp_bind (append _ _)%E. wp_proj.
      iApply ("IH" with "Hxs Hys"). iNext.
      iIntros (l1') "Happ". wp_let. wp_proj. wp_store.
      iApply "H". iExists hd, l1'. by iFrame.
  Qed.
End exercise4_24.

Section exercise4_25.
  Definition append': val :=
    rec: "append'" "l" "l'" :=
      let: "go" := rec: "f" "h" "p" :=
        match: "h" with
          NONE => "p" <- (Fst !"p", "l'")
        | SOME "x2" => "f" (Snd !"x2") "x2"
        end
      in match: "l" with
           NONE => "l'"
         | SOME "x2" => "go" (Snd !"x2") "x2";; "l"
         end.

  Lemma append'_go_spec l' ys :
    ∀ x xs h p,
    {{{ p ↦ (x, h) ∗ is_list h xs ∗ is_list l' ys }}}
      (rec: "f" "h" "p" :=
        match: "h" with
          NONE => "p" <- (Fst ! "p", l')
        | SOME "x2" => "f" (Snd ! "x2") "x2"
        end
      )%V h #p
    {{{ v, RET v; ∃ h, p ↦ (x, h) ∗ is_list h (xs ++ ys) }}}.
  Proof.
    iIntros (x xs h p ϕ) "(Hp & Hh & Hl') H".
    wp_pures. iLöb as "IH" forall (x xs h p ϕ).
    destruct xs as [| x' xs]; iSimplifyEq.
    - wp_match. wp_load. wp_proj. wp_store.
      iApply "H". iExists l'. by iFrame.
    - iDestruct "Hh" as (hd l1) "(% & Hhd & Hh')". iSimplifyEq.
      wp_match. wp_load. wp_proj. wp_pures.
      iApply ("IH" with "[$Hhd] [$Hh'] [$Hl'] [Hp H]").
      iIntros (v) "Hh". iApply "H".
      iDestruct ("Hh") as (h) "[Hhd Hxy]".
      iExists (SOMEV #hd). iFrame.
      iExists hd, h. by iFrame.
  Qed.

  Lemma append'_spec l l' xs ys :
    {{{ is_list l xs ∗ is_list l' ys }}}
      append' l l'
    {{{ v, RET v; is_list v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    wp_rec. wp_let. wp_pures.
    destruct xs as [|x xs]; iSimplifyEq.
    - wp_match. by iApply "H".
    - iDestruct "Hxs" as (hd l1) "(% & Hl & Hxs)". subst.
      wp_match. wp_load. wp_proj.
      wp_bind ((rec: _ _ _ := _)%V _ _)%I.
      wp_apply (append'_go_spec with "[$Hl $Hxs $Hys]").
      iIntros (v) "H'". wp_seq. iApply "H".
      iDestruct "H'" as (h) "[Hhd Hxy]".
      iExists hd, h. by iFrame.
  Qed.
End exercise4_25.

Section exercise4_26.
  Definition length: val :=
    rec: "length" "l" :=
      match: "l" with
        NONE => #0
      | SOME "hd" => "length" (Snd !"hd") + #1
      end.

  Lemma length_spec l xs :
    {{{ is_list l xs }}}
      length l
    {{{ RET #(List.length xs); is_list l xs }}}.
  Proof.
    iIntros (ϕ) "Hl H".
    iLöb as "IH" forall (l xs ϕ). wp_rec.
    destruct xs as [|x xs]; iSimplifyEq.
    - wp_match. by iApply "H".
    - iDestruct "Hl" as (hd l') "(% & Hhd & Hl')". iSimplifyEq.
      wp_match. wp_load. wp_proj. wp_bind (length _).
      iApply ("IH" with "[$Hl']"). iNext.
      iIntros "Hl". wp_op. iSimpl.
      assert (H: (List.length xs + 1)%Z = S (List.length xs)).
      { lia. }
      rewrite H. iApply "H". iExists hd, l'. by iFrame.
  Qed.
End exercise4_26.

Section exercise4_27.
  (* Appends the last [n] values of [l'] to [l]. *)
  Definition append_n: val :=
    rec: "append_n" "l" "l'" "n" :=
      if: (length "l'") ≤ "n"
      then append "l" "l'"
      else match: "l'" with
        NONE => "l"
      | SOME "hd" =>
          if: "n" ≤ #0
          then "l"
          else "append_n" "l" (Snd !"hd") ("n" - #1)
      end.

  Lemma append_n_spec l l' xs ys n :
    {{{ is_list l xs ∗ is_list l' ys }}}
      append_n l l' #n
    {{{ v, RET v; ∃ ys1 ys2, ⌜List.length ys2 ≤ n⌝ ∗
       ⌜ys = (ys1 ++ ys2)⌝ ∗ is_list v (xs ++ ys2)
    }}}.
  Proof.
    iIntros (ϕ) "[Hl Hl'] H".
    iLöb as "IH" forall (l l' xs ys n ϕ).
    wp_rec. do 2 wp_let. wp_apply (length_spec with "Hl'").
    iIntros "Hl'". wp_op.
    case_bool_decide; [wp_if_true|wp_if_false].
    - wp_apply (append_spec with "[$Hl $Hl']").
      iIntros (v) "Hxy". iApply "H".
      iExists [], ys. iFrame. iPureIntro. split; [lia|done].
    - destruct ys as [|y ys]; iSimplifyEq.
      + wp_match. iApply "H".
        iExists [], []. do 2 rewrite app_nil_r. iFrame. iPureIntro.
        split; [lia|done].
      + iDestruct "Hl'" as (hd l1) "(%Hd & Hy & Hl1)". subst.
        wp_match. wp_op. case_bool_decide; [wp_if_true|wp_if_false].
        * iApply "H". iExists (y :: ys), [].
          do 2 rewrite app_nil_r. iFrame.
          iPureIntro. unfold List.length. split; [lia|done].
        * wp_load. wp_proj.
          assert ((n - 1)%Z = (n - 1)%nat) as Hn. { lia. }
          rewrite Hn.
          iApply ("IH" with "[$Hl] [$Hl1] [H Hy]"). iNext.
          iIntros (v) "H'".
          iDestruct "H'" as (ys1 ys2) "(%Hs2 & %Hys & Hv)".
          iApply "H".
          iExists (y :: ys1), ys2.
          iFrame. iPureIntro. rewrite Hys. split; [lia|done].
  Qed.
End exercise4_27.

Section example4_28.
  Definition rev: val :=
    rec: "rev" "l" "acc" :=
      match: "l" with
        NONE => "acc"
      | SOME "hd" =>
          let: "h" := Fst ! "hd" in
          let: "t" := Snd ! "hd" in
          "hd" <- ("h", "acc");;
          "rev" "t" "l"
      end.

  Lemma rev_spec l vs :
    ∀ acc us,
    {{{ is_list l vs ∗ is_list acc us }}}
      rev l acc
    {{{ v, RET v; is_list v (List.rev vs ++ us) }}}.
  Proof.
    iIntros (acc us ϕ) "[Hl Hacc] H".
    iLöb as "IH" forall (l vs acc us ϕ). wp_rec. wp_let.
    destruct vs as [|x vs]; iSimplifyEq.
    - wp_match. iApply "H". by iFrame.
    - iDestruct "Hl" as (hd l') "(% & Hhd & Hl')". subst.
      wp_match. do 2 (wp_load; wp_proj; wp_let). wp_store.
      iApply ("IH" $! _ _ _ (x :: us) with "[$Hl'] [Hhd Hacc] [H]");
        [iExists hd, acc; by iFrame|iNext].
      iIntros (v) "Hv". iApply "H".
      assert (H: List.rev vs ++ x :: us = (List.rev vs ++ [x]) ++ us).
      { by rewrite <- app_assoc. }
      by rewrite <- H.
  Qed.

  Lemma is_list_empty : ⊢ is_list NONEV [].
  Proof. by iIntros. Qed.

  Lemma rev_spec' l vs :
    {{{ is_list l vs }}}
      rev l NONEV
    {{{ v, RET v; is_list v (List.rev vs) }}}.
  Proof.
    iIntros (ϕ) "Hl H".
    wp_apply (rev_spec l vs with "[Hl] [H]");
      [iFrame; by iApply is_list_empty|iNext].
    rewrite app_nil_r. iIntros (v) "H'". by iApply "H".
  Qed.
End example4_28.

Section exercise4_30.
  Lemma rev_involutive l vs :
    {{{ is_list l vs }}}
      rev (rev l NONEV) NONEV
    {{{ v, RET v; is_list v vs }}}.
  Proof.
    iIntros (ϕ) "Hl H".
    wp_bind (rev l _).
    wp_apply (rev_spec' with "[$Hl] [H]"). iNext.
    iIntros (v) "Hv".
    wp_apply (rev_spec' with "[$Hv] [H]"). iNext.
    by rewrite List.rev_involutive.
  Qed.
End exercise4_30.
