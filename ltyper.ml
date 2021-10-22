type lterm = Var of string | App of lterm * lterm | Abs of string * lterm

type ltype = TVar of string | Arr of ltype * ltype

type equa = (ltype * ltype) list

let rec pretty_printer term =
  match term with
  | Var s ->
      s
  | App (m, n) ->
      "(" ^ pretty_printer m ^ " " ^ pretty_printer n ^ ")"
  | Abs (x, m) ->
      "(fun " ^ x ^ " -> " ^ pretty_printer m ^ ")"

let rec print_type (t : ltype) : string =
  match t with
  | TVar x ->
      x
  | Arr (m, n) ->
      "(" ^ print_type m ^ " -> " ^ print_type n ^ ")"

let cvar s = Var s

let cvar_type (s : string) : ltype = TVar s

let carr_type l1 l2 = Arr (l1, l2)

let clam s m = Abs (s, m)

let capp n m = App (n, m)

let rec stype_egal (t1 : ltype) (t2 : ltype) : bool =
  match (t1, t2) with
  | TVar x, TVar y ->
      x = y
  | TVar x, _ ->
      false
  | _, TVar x ->
      false
  | Arr (l1, l2), Arr (s1, s2) ->
      stype_egal l1 s1 && stype_egal l2 s2

let var_counter : int ref = ref 0

let new_var () : string =
  var_counter := !var_counter + 1 ;
  "T" ^ string_of_int !var_counter

exception UnboundValue

let rec gen_equas (env : (string * ltype) list) (t : lterm) (target : ltype) :
    equa =
  match t with
  | Var x -> (
    try
      let r = List.assoc x env in
      [(target, r)]
    with Not_found -> raise UnboundValue )
  | Abs (x, m) ->
      let t1 = new_var () and t2 = new_var () in
      let arr = Arr (TVar t1, TVar t2) in
      (target, arr) :: gen_equas ((x, TVar t1) :: env) m (TVar t2)
  | App (f, x) ->
      let t1 = new_var () in
      gen_equas env f (Arr (TVar t1, target)) @ gen_equas env x (TVar t1)

let rec occur_check v = function
  | TVar x ->
      x = v
  | Arr (t1, t2) ->
      occur_check v t1 || occur_check v t2

let rec substitue_type v ts t =
  match t with
  | TVar x ->
      if x = v then ts else t
  | Arr (t1, t2) ->
      Arr (substitue_type v ts t1, substitue_type v ts t2)

let rec substitue_partout (v : string) (ts : ltype) (eqs : equa) : equa =
  match eqs with
  | [] ->
      []
  | (t1, t2) :: xs ->
      (substitue_type v ts t1, substitue_type v ts t2)
      :: substitue_partout v ts xs

let rec unification_etape eqs target =
  match eqs with
  | [] ->
      []
  | (t1, t2) :: xs when t1 = target || t2 = target ->
      unification_etape (xs @ [(t1, t2)]) target
  | (t1, t2) :: xs when t1 = t2 ->
      xs
  | (TVar x, t2) :: xs ->
      if not (occur_check x t2) then substitue_partout x t2 xs
      else failwith "error unification"
  | (Arr (t1, t2), Arr (t3, t4)) :: xs ->
      (t1, t3) :: (t2, t4) :: xs
  | _ ->
      failwith "error unification"

let rec unification eqs timeout target =
  if timeout <= 0 then failwith "timeout"
  else
    match eqs with
    | [] ->
        failwith "error unification"
    | [x] ->
        x
    | x ->
        unification (unification_etape x target) (timeout - 1) target

let get_eq_target eq target =
  match eq with t1, t2 -> if target = t1 then t2 else t1

let typer (term : lterm) =
  let target = cvar_type (new_var ()) in
  let eqs = gen_equas [] term target in
  let unif_res = unification eqs 10000 target in
  get_eq_target unif_res target

let _ =
  print_endline (pretty_printer (Var "x")) ;
  print_endline (pretty_printer (App (Abs ("x", Var "x + 2"), Var "y"))) ;
  print_endline
    (string_of_bool
       (stype_egal
          (Arr (TVar "int", TVar "int"))
          (Arr (TVar "int", TVar "int")) ) )
