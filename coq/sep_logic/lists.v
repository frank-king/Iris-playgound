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

Section case_study_foldr.
  Definition foldr : val :=
    rec: "foldr" "f" "a" "l" :=
      match: "l" with
        NONE => "a"
      | SOME "hd" =>
          let: "h" := Fst ! "hd" in
          let: "t" := Snd ! "hd" in
          "f" "h" ("foldr" "f" "a" "t")
      end.

  Fixpoint all (P : val → iProp) xs : iProp :=
    match xs with
    | [] => True
    | x :: xs' => P x ∗ all P xs'
    end.

  Lemma foldr_spec :
    ∀ P I (f: val) (a : val) xs l,
    {{{ is_list l xs ∗ all P xs ∗ I [] a ∗
      ⌜(∀ x a' ys,
        {{{ P x ∗ I ys a' }}} f x a' {{{r, RET r; I (x :: ys) r }}}
      )⌝ }}}
      foldr f a l
    {{{ r, RET r; is_list l xs ∗ I xs r }}}.
  Proof.
    iIntros (P I f a xs l Φ) "(Hl & HP & HI & %Hf) H".
    iLöb as "IH" forall (xs l Φ). wp_rec. do 2 wp_let.
    destruct xs; iSimplifyEq.
    - wp_match. iApply "H". by iFrame.
    - iDestruct "Hl" as (hd l') "(%Hl & Hhd & Hl)". subst.
      wp_match. do 2 (wp_load; wp_proj; wp_let).
      wp_bind (foldr _ _ _). iDestruct "HP" as "[HP HP']".
      iApply ("IH" with "[$] [$] [$] [HP Hhd H]").
      iNext. iIntros (r) "[Hl' HI]".
      wp_apply (Hf with "[$HP HI//]").
      iIntros (r') "HI". iApply "H". iFrame.
      iExists hd, l'. by iFrame.
  Qed.
End case_study_foldr.

Section sum_list. (* exercise5_2 *)
  Definition sum_list : val :=
    rec: "sum_list" "l" :=
      let: "f" := (λ: "x" "y", "x" + "y")%V in foldr "f" #0 "l".

  Fixpoint list_sum (xs : list Z) : Z :=
    match xs with
    | [] => 0
    | x :: xs' => x + list_sum xs'
    end.

  Inductive is_sum_of_list_v : list val → val → Prop :=
    | sum_emp : is_sum_of_list_v [] #0
    | sum_cons : ∀ vs (n : Z) (ns : Z),
        is_sum_of_list_v vs #ns →
        is_sum_of_list_v (#n :: vs) #(n + ns).

  Definition is_sum_of_list l s : iProp := ⌜is_sum_of_list_v l s⌝.

  Definition is_nat v : iProp := ∃ x : Z, ⌜v = #x⌝.

  Inductive val_list_is_nat_list : list val → list Z → Prop :=
    | nl_emp : val_list_is_nat_list [] []
    | nl_cons : ∀ (x : Z) vs xs,
        val_list_is_nat_list vs xs →
        val_list_is_nat_list (#x :: vs) (x :: xs).

  Lemma all_is_nat_pesist :
    ∀ vs, all is_nat vs ⊢ □ all is_nat vs.
  Proof.
    induction vs; [by iIntros|].
    iIntros "[%Ha H]". iPoseProof (IHvs with "H") as "#H'".
    iModIntro. destruct Ha as [x Ha]. subst.
    iSplit; [by iExists x|]. iApply "H'".
  Qed.

  Lemma nat_list_is_all_nat :
    ∀ vs xs,
    ⌜val_list_is_nat_list vs xs⌝ ⊢ □ all is_nat vs.
  Proof.
    iIntros (vs xs) "%H". iApply (all_is_nat_pesist).
    generalize dependent xs. induction vs; [done|].
    iIntros. inversion H. subst.
    iSplit; [by iExists x|]. apply (IHvs _ H3).
  Qed.

  Lemma list_all_nat_is_nat_list l vs :
    is_list l vs ∗ □ all is_nat vs ⊢
      (∃ xs, is_list_nat l xs ∗ ⌜val_list_is_nat_list vs xs⌝).
  Proof.
    iIntros "[Hl #Hv]".
    iInduction vs as [|v vs] "IH" forall (l);
        [iExists []; iFrame; iPureIntro; constructor|].
    iDestruct "Hl" as (hd l') "(%Hl & Hhd & Hl)". subst.
    iDestruct "Hv" as "[Hx Hv]". iDestruct "Hx" as (x) "%Hx". subst.
    iSpecialize ("IH" with "[$] [$]").
    iDestruct "IH" as (xs) "[IHl' %Hv]".
    iExists (x :: xs). iSplitL; [iExists hd, l'; by iFrame|].
    iPureIntro. by constructor.
  Qed.

  Lemma list_iff_list_nat vs xs :
    val_list_is_nat_list vs xs →
      ∀ l, is_list l vs ⊣⊢ is_list_nat l xs.
  Proof.
    iIntros.
    iInduction H as [|v x vs xs Hvx H IH] "IH" forall (l);
        [by iSplit|subst].
    iSplit; iIntros "H";
      iDestruct "H" as (hd l') "(%Hl & Hhd & Hl)"; subst;
      iExists hd, l'; iFrame; iSplitR; [done| |done| ];
      by iApply "IH".
  Qed.

  Lemma nat_list_is_list_all_nat l xs :
    is_list_nat l xs ⊢
      (∃ vs, is_list l vs ∗ ⌜val_list_is_nat_list vs xs⌝).
  Proof.
    iIntros "Hl".
    iInduction xs as [|x xs] "IH" forall (l);
        [iExists []; iFrame; iPureIntro; constructor|].
    iDestruct "Hl" as (hd l') "(%Hl & Hhd & Hl)". subst. fold is_list_nat.
    iPoseProof ("IH" with "Hl") as (vs) "[Hl' %H]".
    iExists (#x :: vs). iSplitL; [|iPureIntro; by constructor].
    iExists hd, l'. by iFrame.
  Qed.

  Lemma sum_list_spec :
    ∀ l xs,
    {{{ is_list_nat l xs }}}
      sum_list l
    {{{ r, RET r; is_list_nat l xs ∗
      ⌜∃ n : Z, r = #n ∧ n = list_sum xs⌝ }}}.
  Proof.
    iIntros (l xs Φ) "Hl H". unfold sum_list. wp_rec. wp_pures.
    iPoseProof (nat_list_is_list_all_nat with "Hl")
      as (vs) "[Hl #Hv]".
    iPoseProof (nat_list_is_all_nat with "Hv") as "#Hv'".
    wp_apply (
      foldr_spec is_nat is_sum_of_list _ _ vs
      with "[$Hl $Hv'] [H]"); [iSplitL; [iPureIntro; constructor|]|].
    - iPureIntro. iIntros (x a' ys Φ') "[Hx Hys] H".
      iDestruct "Hx" as (n) "%Hx". subst. wp_lam. wp_let.
      iStopProof. iIntros "[%H H]".
      inversion H; iSimplifyEq; wp_op; iApply "H"; iPureIntro;
        by constructor.
    - iStopProof. iIntros "(#[%H Hv] & H)".
      iNext. iIntros (r) "[Hl %Hvs]".
      iPoseProof (list_iff_list_nat _ _ H) as "Hvx".
      iPoseProof ("Hvx" with "Hl") as "Hl".
      iApply "H". iFrame. iPureIntro.
      generalize dependent xs.
      induction Hvs; intros xs H; inversion H; subst; [by exists 0| ].
      exists (n + ns)%Z. split; [done|].
      apply IHHvs in H3. destruct H3 as (n1 & Hns & IH).
      inversion Hns; subst. by simpl.
  Qed.
End sum_list. (* exercise5_2 *)

Section filter. (* exercise5_3 *)
  Definition filter : val :=
    rec: "filter" "p" "l" :=
      let: "f" :=
        λ: "x" "xs",
          if: "p" "x" then SOME (ref ("x", "xs")) else "xs"
      in foldr "f" NONEV "l".

  Definition iTrue (x : val) : iProp := True.

  Lemma all_true_is_true : ∀ l, ⊢ all iTrue l.
  Proof. induction l; [done|]. by iSplitL. Qed.

  Lemma filter_spec :
    ∀ P (p : val) l xs,
      {{{ is_list l xs ∗ ⌜(∀ x : val,
        {{{ True }}}
          p x
        {{{ (v : bool), RET #v; ⌜P x = v⌝ }}})⌝
      }}}
        filter p l
      {{{ r, RET r; is_list l xs ∗ is_list r (List.filter P xs) }}}.
  Proof.
    iIntros (P p l xs Φ) "[Hl %H] H". wp_rec. wp_let. wp_pures.
    wp_apply (
      foldr_spec iTrue (λ xs l, is_list l (List.filter P xs))
      with "[$Hl] [H]"); [|done].
    iSplitL; [iApply all_true_is_true|].
    iSplitL; [done|iPureIntro].
    iIntros (x l' ys Φ') "[_ Hl'] H". wp_lam. wp_let.
    wp_apply H; [done|iIntros (v) "%Hv"].
    destruct (v); [wp_if_true|wp_if_false].
    - wp_alloc hd as "Hhd". wp_pures. iApply "H". simpl.
      rewrite Hv. iExists hd, l'. by iFrame.
    - iApply "H". simpl. by rewrite Hv.
  Qed.
End filter.  (* exercise5_3 *)
