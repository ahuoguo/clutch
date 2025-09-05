From clutch Require Export clutch.
Set Default Proof Using "Type*".

Section fresh_refl.
  Context `{!clutchRGS Σ}.

  Definition fresh_name : expr := 
    ref #().

  (* Lemma lemma_lrel_car :
    (∀ (l : lrel Σ) a b, l a b = l.(lrel_car) a b).
  Proof.
    intros l a b.
    unfold lrel_car.
    destruct l; auto.
  Qed. *)

  Lemma fresh_name_reflexivity :
    ⊢ REL fresh_name << fresh_name : lrel_ref lrel_unit.
  Proof.
    unfold fresh_name.
    rel_alloc_l xl as "Hx".
    rel_alloc_r yl as "Hy".
    rel_values.
    (* unfold lrel_ref. *)
    (* Print lrel. *)
    (* Set Printing Implicit. *)
    (* Set Printing Coercions. *)
    (* Print LRel. *)
    (* Print lrel_car. *)

    (* lrel_unit. *)
    (* rewrite //=. *)
    rewrite /lrel_ref /lrel_unit.
    unfold lrel_car.
    (* rewrite lemma_lrel_car. *)
    (* unfold lrel_car. (* Q: WHY THE FUCK YOU CAN UNFOLE THIS THING ???? *) *)
                      (* PS: PHILIP ALSO HAS THE SAME QUESTION *)
    (* Ans: becuase if you print the implicit and coercions, you get the `lrel_car` thing that applied to a record type *)
    iExists xl, yl. repeat (iSplitR; auto). (* why using iSplit doesn't work here? Ans: bc that really only deals with ∧ ...*)
    (* Print inv_alloc. *)
    (* Q: why there's a basic update for all the invariant rules *)
    (* Ans: it's actually a fancy update, you want the upd modality for the masks (see wsat) *)
    iApply inv_alloc.
    iNext.
    iExists #(), #().
    by iFrame.
  Qed.

(* 
  Lemma fresh_name_ctx_ref_alt :
    ∅ ⊨ fresh_name ≤ctx≤ fresh_name : TRef TUnit.
  Proof.
    eapply (refines_sound clutchRΣ). intros.
    simpl.
    (* TODO: how to put this in the section... *)
    apply fresh_name_reflexivity.
  Qed. *)

End fresh_refl.

Lemma fresh_name_ctx_ref :
  ∅ ⊨ fresh_name ≤ctx≤ fresh_name : TRef TUnit.
Proof.
  unfold fresh_name.
  apply ctx_refines_reflexive.
Qed.

Lemma fresh_name_ctx_eq :
  ∅ ⊨ fresh_name =ctx= fresh_name : TRef TUnit.
Proof.
  unfold ctx_equiv.
  auto using fresh_name_ctx_ref.
Qed.

Lemma fresh_name_ctx_ref_alt :
  ∅ ⊨ fresh_name ≤ctx≤ fresh_name : TRef TUnit.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  (* TODO: this simpl is important, otherwise rocq runs for a LONG TIME *)
  simpl.
  (* TODO: how to put this in the section..., or why the logical refinement is in it's own section  *)

  apply fresh_name_reflexivity.
Qed.
