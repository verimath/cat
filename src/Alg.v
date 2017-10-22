Require Export Category.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

Section alg_def.

Variable (C : Category).
Variable (F : Functor C C).

Structure Alg_ob : Type :=
  { Ob_alg_ob :> C
  ; Mor_alg_ob :> F Ob_alg_ob --> Ob_alg_ob
  }.

Definition Alg_law (a : Alg_ob) (b : Alg_ob) (h : a --> b) :=
  a o h =_S FMor F h o b .

Structure Alg_mor (a : Alg_ob) (b : Alg_ob) : Type :=
  { Mor_alg_mor :> a --> b
  ; Prf_Alg_law :> Alg_law Mor_alg_mor
  }.

Section equal_alg_mor.

Variables a b : Alg_ob.

Definition Equal_Alg_mor (f g : Alg_mor a b) :=
  Mor_alg_mor f =_S Mor_alg_mor g 
  .

Lemma Equal_Alg_mor_equiv : Equivalence Equal_Alg_mor.
Proof.
unfold Equal_Alg_mor.
apply Build_Equivalence.
red.
intro.
apply Refl.
apply Build_Partial_equivalence.
red.
intros x y z.
apply Trans.
red.
intros x y.
apply Sym.
Qed.

Canonical Structure Alg_mor_setoid : Setoid := Equal_Alg_mor_equiv.

End equal_alg_mor.

Section comp_alg_mor.

Variables (a b c : Alg_ob) (f : Alg_mor a b) (g : Alg_mor b c).

Lemma Comp_Alg_mor_law : Alg_law (f o g).
Proof.
red.
apply Trans with ((a o f) o g).
apply Ass.
apply Trans with ((FMor F f o b) o g).
apply Comp_r.
apply Prf_Alg_law.
apply Trans with (FMor F f o (b o g)).
apply Ass1.
apply Trans with ((FMor F f o FMor F g o c)).
apply Comp_l.
apply Prf_Alg_law.
apply Trans with ((FMor F f o FMor F g) o c).
apply Ass.
apply Comp_r.
apply FComp1.
Qed.

Definition Comp_Alg_mor: Alg_mor a c :=
  Build_Alg_mor Comp_Alg_mor_law.

End comp_alg_mor.

Lemma Comp_Alg_mor_congl : Congl_law Comp_Alg_mor.
Proof.
red.
intros a b c f g h eq.
simpl.
unfold Comp_Alg_mor.
unfold Equal_Alg_mor.
red.
apply Comp_l.
apply eq.
Qed.

Lemma Comp_Alg_mor_congr : Congr_law Comp_Alg_mor.
Proof.
red.
intros a b c f g h eq.
simpl.
unfold Comp_Alg_mor.
unfold Equal_Alg_mor.
red.
apply Comp_r.
apply eq.
Qed.

Definition Comp_Alg := Build_Comp Comp_Alg_mor_congl Comp_Alg_mor_congr.

Lemma Assoc_Alg : Assoc_law Comp_Alg.
Proof.
unfold Assoc_law.
intros a b c d f g h.
unfold Cat_comp.
unfold Comp_Alg.
simpl.
unfold Alg_mor_setoid, Comp_Alg_mor.
unfold Equal_Alg_mor.
simpl.
apply Ass.
Qed.

Section id_alg_mor.
Variables (a : Alg_ob).

Lemma Id_Alg_mor_law : Alg_law (Id a).
Proof.
red.
apply Trans with (Mor_alg_ob a).
apply Idr1.
apply Trans with (Id (F a) o a).
apply Idl1.
apply Comp_r.
apply FId1.
Qed.

Definition Id_Alg : Alg_mor a a := Build_Alg_mor Id_Alg_mor_law.

End id_alg_mor.

Lemma Idl_Alg : Idl_law Comp_Alg Id_Alg.
Proof.
red.
intros a b f.
unfold Cat_comp.
unfold Comp_Alg.
simpl.
unfold Equal_Alg_mor.
simpl.
apply Idl.
Qed.

Lemma Idr_Alg : Idr_law Comp_Alg Id_Alg.
Proof.
red.
intros a b f.
unfold Cat_comp.
unfold Comp_Alg.
simpl.
unfold Equal_Alg_mor.
simpl.
apply Idr.
Qed.

Canonical Structure Alg := Build_Category Assoc_Alg Idl_Alg Idr_Alg.

End alg_def.


Require Export CatProperty.

Section initial_algebra.

Variable (C : Category).
Variable (F : Functor C C).
Variable (initial : Initial (Alg F)).

Let muF := Initial_ob initial.
Let inF := Mor_alg_ob muF.
Let fold := MorI initial.
Let FmuF := Build_Alg_ob (FMor F muF).

Lemma inF_Alg_law : Alg_law (a:=FmuF) (b:=muF) inF.
Proof.
apply Refl.
Qed.

Let inF' := Build_Alg_mor inF_Alg_law.
Let unInF' := fold (Build_Alg_ob (FMor F inF)).
Let unInF := Mor_alg_mor unInF'.

Lemma lem1 : RIso_law inF' unInF'.
unfold RIso_law.
apply (UniqueI (unInF' o inF') (Id muF)).
Qed.

Lemma lem2 : RIso_law unInF inF.
unfold RIso_law.
apply Trans with (FMor F unInF o FMor F inF).
apply (Prf_Alg_law unInF').
apply Trans with (FMor F (unInF o inF)).
apply FComp1.
apply Trans with (FMor F (Id (Ob_alg_ob muF))).
apply FPres.
apply lem1.
apply FId.
Qed.

Lemma LambekLemma : AreIsos inF unInF.
unfold AreIsos.
split.
apply lem1.
apply lem2.
Qed.

End initial_algebra.
