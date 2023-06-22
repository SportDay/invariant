open Printf

(* Définitions de terme, test et programme *)
type term = 
  | Const of int
  | Var of int
  | Add of term * term
  | Mult of term * term

type test =
  | Equals of term * term
  | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)

type program = {nvars : int;
                inits : term list;
                mods : term list;
                loopcond : test;
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string`
   et `str_of_test : test -> string` qui convertissent des termes
   et des tests en chaînes de caractères du format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term t =
  match t with
  | Const x -> string_of_int x
  | Var x -> "x" ^ string_of_int x
  | Add (a, b) -> "(+ " ^ str_of_term a ^ " " ^ str_of_term b ^ ")"
  | Mult (a, b) -> "(* " ^ str_of_term a ^ " " ^ str_of_term b ^ ")"

let str_of_test t =
  match t with
  | Equals (a, b) -> "(= " ^ str_of_term a ^ " " ^ str_of_term b ^ ")"
  | LessThan (a, b) -> "(< " ^ str_of_term a ^ " " ^ str_of_term b ^ ")"

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne
   de caractères qui exprime que le tuple (t1, ..., tk) est dans
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne
   "(Inv x1 10)".
*)
let str_condition l =
  let rec loop l' str =
    match l' with
    | [] -> str
    | h :: t -> loop t (str ^ " " ^ str_of_term h)
  in let s = loop l "" in "(Invar" ^ s ^ ")"

(* Question 3. Écrire une fonction
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall n s =
  let rec loop str x =
    if x = n then str ^ " (x" ^ string_of_int x ^ " Int)) (" ^ s ^ ")"
    else if x = 1 then loop ("(x" ^ string_of_int x ^ " Int)") (x + 1) (* pour l'espace en trop *)
    else loop (str ^ " (x" ^ string_of_int x ^ " Int)") (x + 1)
  in let s' = loop "" 1 in str_assert ("(forall (" ^ s' ^ ")")

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let build_var x =
    let rec loop x' str =
      if x' = x then (str ^ " x" ^ string_of_int x')
      else loop (x' + 1) (str ^ " x" ^ string_of_int x') in
    "(Invar" ^ (loop 1 "") ^ ")"

let tmp_loop_condition p = "=> (and " ^ (build_var p.nvars) ^ " " ^ (str_of_test p.loopcond) ^ ") " ^ (str_condition p.mods)
let tmp_assertion_condition p = "=> (and " ^ (build_var p.nvars) ^ " (not " ^ (str_of_test p.loopcond) ^ ")) " ^ (str_of_test p.assertion)

let smtlib_of_wa p =
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^ ") Bool)" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^ str_assert_forall p.nvars (tmp_loop_condition p)  in
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert_forall p.nvars (tmp_assertion_condition p) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}


let () = Printf.printf "---------- Test 1 ----------\n\n%s\n" (smtlib_of_wa p1)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

(*
Code java:

int i = 0;
int v = 1;
int y = 476;
while (i < 9) {
    v = v * 2;
    y = y + i;
    i = i + 1;
}
assert(v == y);

*)
let p2 = {nvars = 3;
           (*       i               v       y*)
          inits = [(Const 0) ; (Const 1); (Const 476)];
          mods = [Add ((Var 1), (Const 1)); Mult ((Var 2), (Const 2)); Add ((Var 3), (Var 1))];
          loopcond = LessThan ((Var 1),(Const 9));
          assertion = Equals ((Var 2),(Var 3))}

let () = Printf.printf "---------- Test 2 ----------\n\n%s\n" (smtlib_of_wa p2)
