From stdpp Require Export stringmap fin_map_dom gmap.
From clutch Require Export clutch clutch.lib.flip clutch.lib.conversion.
From clutch.common Require Import exec.
From clutch.prob_lang.typing Require Import tychk.

Set Default Proof Using "Type*".

(** If we assume that we can freely pick presampling tapes to read from when
    resolving probabilistic choices, we can show refinements/equivalences that
    do not hold. *)
Section counterexample_annotation.
  Context `{!clutchRGS Σ}.

  Definition refines_tape_unsound :=
    ∀ K E (A : lrel Σ) α N n ns e',
    α ↪ (N; n::ns) ∗
    (α ↪ (N; ns) -∗  REL fill K (Val #n) << e' @ E : A)
    ⊢ REL fill K (rand #N) << e' @ E : A.
  Print refines_tape_unsound.

  Definition flip : expr := rand #1.

  Definition flip_ors : expr :=
    let: "x" := rand #1 in
    let: "y" := rand #1 in
    if: "x" = #1 then #1 else "y".

  Lemma counterexample_annotation α1 α2 :
    refines_tape_unsound →
    (α1 ↪ (1%nat; [])) ∗ (α2 ↪ (1%nat; []))
    ⊢ REL flip << flip_ors  : lrel_int.
  Proof.
    iIntros (refines_tape_unsound) "[Hα1 Hα2]". rewrite /flip_ors /flip.
    rel_apply (refines_couple_tape_rand _ _ _ _ _ α1); iFrame.
    iIntros (n1) "Hα1 /=".
    rel_pures_r.
    rel_apply (refines_couple_tape_rand _ _ _ _ _ α2); iFrame.
    iIntros (n2) "Hα2 /=".
    rel_pures_r.
    case_bool_decide.
    - rewrite -H. rel_apply (refines_tape_unsound _ _ _ α1).
      (* TODO: how to rewrite this H' *)
      admit.
    - admit. (* TODO: not sure how to apply the other lemma.. *)
      (* rel_apply (refines_tape_unsound _ _ _ α2). *)



  Admitted.


End counterexample_annotation.



