type 'a plist = Empty | Cons of 'a * 'a plist

type pterm =
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Int of int
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | List of pterm plist
  | Hd of pterm
  | Tail of pterm
  | If_Empty of pterm * pterm * pterm
  | If_Zero of pterm * pterm * pterm
  | Let of string * pterm * pterm
  | Let_Rec of string * pterm * pterm

let t = Let ("a", Int 5, Add (Int 4, Var "a"))

type ptype =
  | TVar of string
  | Arr of ptype * ptype
  | N
  | TList of ptype
  | Forall of string list * ptype

type equa = (ptype * ptype) list

type typing_error = Unbound_var of string | Clash of ptype * ptype

exception Type_error of typing_error

let get_head l =
  match l with Empty -> failwith "list is empty" | Cons (x, _) -> x

let get_tail l =
  match l with Empty -> failwith "list is empty" | Cons (_, xs) -> xs

let rec print_string_list l =
  let rec aux = function Empty -> "" | Cons (x, xs) -> x ^ ", " ^ aux xs in
  "[" ^ aux l ^ "]"

let rec print_pterm_list l =
  let rec aux = function
    | Empty ->
        ""
    | Cons (x, xs) ->
        pretty_printer x ^ ", " ^ aux xs
  in
  "[" ^ aux l ^ "]"

and pretty_printer term =
  match term with
  | Var s ->
      s
  | App (m, n) ->
      "(" ^ pretty_printer m ^ " " ^ pretty_printer n ^ ")"
  | Abs (x, m) ->
      "(fun " ^ x ^ " -> " ^ pretty_printer m ^ ")"
  | Int n ->
      string_of_int n
  | Add (a, b) ->
      pretty_printer a ^ " + " ^ pretty_printer b
  | Sub (a, b) ->
      pretty_printer a ^ " - " ^ pretty_printer b
  | List l ->
      print_pterm_list l
  | Hd l ->
      "Hd(" ^ pretty_printer l ^ ")"
  | Tail l ->
      "Tail(" ^ pretty_printer l ^ ")"
  | If_Empty (l, e1, e2) ->
      "if " ^ pretty_printer l ^ " == empty then " ^ pretty_printer e1
      ^ pretty_printer e2
  | If_Zero (n, e1, e2) ->
      "if " ^ pretty_printer n ^ " == 0 then " ^ pretty_printer e1
      ^ pretty_printer e2
  | Let (x, e1, e2) ->
      "let " ^ x ^ " = " ^ pretty_printer e1 ^ " in " ^ pretty_printer e2
  | Let_Rec (x, e1, e2) ->
      "let rec " ^ x ^ " = " ^ pretty_printer e1 ^ " in " ^ pretty_printer e2

and print_type t =
  match t with
  | TVar x ->
      x
  | Arr (m, n) ->
      "(" ^ print_type m ^ " -> " ^ print_type n ^ ")"
  | N ->
      "int"
  | TList a ->
      print_type a ^ " list"
  | Forall (l, p) ->
      "Forall " ^ "l" ^ "." ^ print_type p

let var_counter : int ref = ref 0

let new_var () : string =
  var_counter := !var_counter + 1 ;
  "T" ^ string_of_int !var_counter

(* return all type variables of t*)
let get_vars t =
  let rec aux t acc =
    match t with
    | TVar v ->
        if List.mem v acc then acc else v :: acc
    | Arr (t1, t2) ->
        let acc = aux t1 acc in
        aux t2 acc
    | N ->
        acc
    | TList t1 ->
        aux t1 acc
    | Forall (_, t1) ->
        aux t1 acc
  in
  aux t []

let rec remove_all l1 l2 =
  match l1 with
  | [] ->
      []
  | x :: xs ->
      if List.mem x l2 then remove_all xs l2 else x :: remove_all xs l2

let get_free_vars_env (env : (string * ptype) list) : string list =
  let rec aux env acc =
    match env with
    | [] ->
        List.sort_uniq String.compare (List.flatten acc)
    | (_, t) :: xs -> (
      match t with
      | Forall (var, t1) ->
          let vars = get_vars t1 in
          let free_vars = remove_all vars var in
          aux xs (free_vars :: acc)
      | Arr (t1, t2) ->
          aux xs (get_vars t1 :: get_vars t2 :: acc)
      | N ->
          aux xs acc
      | TVar var ->
          aux xs ([var] :: acc)
      | TList t1 ->
          aux xs (get_vars t1 :: acc) )
  in
  aux env []

let get_eq_target eq target =
  match eq with t1, t2 -> if target = t1 then t2 else t1

let rec generalise env t =
  let free_vars = get_free_vars_env env in
  let vars = List.filter (fun v -> not (List.mem v free_vars)) (get_vars t) in
  if vars = [] then t else Forall (vars, t)

let rec gen_equas (env : (string * ptype) list) (expr : pterm) (target : ptype)
    : equa =
  match expr with
  | Var x -> (
    try
      let r = List.assoc x env in
      [(target, r)]
    with Not_found -> raise (Type_error (Unbound_var x)) )
  | Abs (x, m) ->
      let t1 = new_var () and t2 = new_var () in
      let arr = Arr (TVar t1, TVar t2) in
      (target, arr) :: gen_equas ((x, TVar t1) :: env) m (TVar t2)
  | App (f, x) ->
      let t1 = new_var () in
      gen_equas env f (Arr (TVar t1, target)) @ gen_equas env x (TVar t1)
  | Add (e1, e2) ->
      ((N, target) :: gen_equas env e1 N) @ gen_equas env e2 N
  | Sub (e1, e2) ->
      ((N, target) :: gen_equas env e1 N) @ gen_equas env e2 N
  | List Empty ->
      []
  | List (Cons (x, xs)) ->
      let var = new_var () in
      ((TList (TVar var), target) :: gen_equas env x (TVar var))
      @ gen_equas env (List xs) (TList (TVar var))
  | Hd (List l) ->
      let var = new_var () in
      [(Forall ([var], Arr (TList (TVar var), TVar var)), target)]
  | Tail (List _) ->
      let var = new_var () in
      [(Forall ([var], Arr (TList (TVar var), TList (TVar var))), target)]
  | Int _ ->
      [(N, target)]
  | If_Zero (c, e1, e2) ->
      gen_equas env c N @ gen_equas env e1 target @ gen_equas env e2 target
  | If_Empty (c, e1, e2) ->
      let var = new_var () in
      gen_equas env c (Forall ([var], TVar var))
      @ gen_equas env e1 target @ gen_equas env e2 target
  | Let (v, e1, e2) ->
      let t0 = typer e1 in
      let t0_g = generalise env t0 in
      gen_equas ((v, t0_g) :: env) e2 target
  | Let_Rec (v, e1, e2) ->
      let t0 = typer e1 in
      let t0_g = generalise env t0 in
      gen_equas ((v, t0_g) :: env) e2 target
  | _ ->
      failwith "equation exception"

and occur_check v = function
  | TVar x ->
      x = v
  | Arr (t1, t2) ->
      occur_check v t1 || occur_check v t2
  | TList t1 ->
      occur_check v t1
  | N ->
      false
  | Forall (_, t1) ->
      occur_check v t1

and substitue_type v ts t =
  match t with
  | TVar x ->
      if x = v then ts else t
  | Arr (t1, t2) ->
      Arr (substitue_type v ts t1, substitue_type v ts t2)
  | N ->
      N
  | TList t1 ->
      TList (substitue_type v ts t1)
  | Forall (vars, t1) ->
      Forall (vars, substitue_type v ts t1)

and substitue_partout (v : string) (ts : ptype) (eqs : equa) : equa =
  match eqs with
  | [] ->
      []
  | (t1, t2) :: xs ->
      (substitue_type v ts t1, substitue_type v ts t2)
      :: substitue_partout v ts xs

and substitue_type_vars (vars : string list) t =
  match vars with
  | [] ->
      t
  | x :: xs ->
      let var = new_var () in
      substitue_type_vars xs (substitue_type x (TVar var) t)

and unification_etape eqs target =
  match eqs with
  | [] ->
      []
  | (Forall (vars, t1), t2) :: xs ->
      (substitue_type_vars vars t1, t2) :: xs
  | (t1, Forall (vars, t2)) :: xs ->
      (substitue_type_vars vars t2, t1) :: xs
  | (TList t1, TList t2) :: xs ->
      (t1, t2) :: xs
  | (t1, t2) :: xs when t1 = target || t2 = target ->
      unification_etape (xs @ [(t1, t2)]) target
  | (t1, t2) :: xs when t1 = t2 ->
      xs
  | (TVar x, t2) :: xs ->
      if not (occur_check x t2) then substitue_partout x t2 xs
      else failwith "error unification_etape"
  | (Arr (t1, t2), Arr (t3, t4)) :: xs ->
      (t1, t3) :: (t2, t4) :: xs
  | _ ->
      failwith "error unification_etape"

and unification eqs timeout target =
  if timeout <= 0 then failwith "timeout"
  else
    match eqs with
    | [] ->
        failwith "error unification"
    | [x] ->
        x
    | x ->
        unification (unification_etape x target) (timeout - 1) target

and typer (term : pterm) =
  let target = TVar (new_var ()) in
  let eqs = gen_equas [] term target in
  let unif_res = unification eqs 10000 target in
  get_eq_target unif_res target

let main () =
  print_endline
    (pretty_printer (Tail (List (Cons (Int 3, Cons (Int 4, Empty))))))
