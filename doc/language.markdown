TT
===

    term t :=
      odvisna teorija tipov z anotacijami
    type ty :=
      verjetno isto kot termi?


CORE EFF
========

    value v :=
      | IsType ty
      | IsTerm t ty
      | 0, 1, 2, ...
      | true, false,
      | fun x -> c
      | handler ...



    pure type A :=
      | nat
      | bool
      | is_term
      | is_type
      | A -> C
      | C => D

    dirty type C :=
      | A


    computation c :=
      # kot v Effu
      | return e
      | let x = c1 in c2
      | with e handle c
      | if e then c1 else c2

      # definirane? operacije
      | lambda x : e => c
      | refl e
      | eq e1 e2
      | e1 @ e2
      | forall x : e, c

      # posebni konstrukti
      | ascribe c e
      | as_type e

    expression e :=
      | Type
      | x
      | 0, 1, 2, ...
      | true, false,
      | fun x -> c
      | handler ...


      c : is_term   e : is_type
    ----------------------------
         ascribe c e : is_term

       e : is_term
    -----------------------
      as_type e : is_type

         e : is_term
    ----------------------
      type_of e : is_term

    --------------------
       Type : is_term

        e : is_term
    ---------------------
       refl e : is_term

      e : is_type      x : is_term |- c : is_term
    ----------------------------------------------
       lambda x : e => c
